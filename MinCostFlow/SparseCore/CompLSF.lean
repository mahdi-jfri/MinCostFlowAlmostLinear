module

public import MinCostFlow.SparseCore.QuotientStepBound
public import MinCostFlow.SparseCore.LSFInit
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Component-wise dynamic LSF wrapper (`CompLSF`)

For possibly disconnected nonempty valid graphs `G₀`, `initLSF` creates
`Θ(|components G₀| · log² n₀)` initial roots, which can exceed `O(m₀ / k)`. This module isolates
component-wise dynamic LSF maintenance `CompLSFState`:

1. `compGraph G₀ C`: connected induced subgraph on each `C ∈ components G₀`, partitioned into
   `largeComps k G₀` (`1 ≤ m_C ∧ k ≤ 4 * m_C`), `tinyComps k G₀` (`1 ≤ m_C ∧ 4 * m_C < k`), and
   `isoComps G₀` (`m_C = 0`).
2. `initLSF_tiny_props` and `initLSF_large_tildeV_le`: `1 ≤ 4 * m_C < k` implies `R_C.card = 1` and
   `tildeC0Base.V.card ≤ 11`, whereas `k ≤ 4 * m_C` implies `tildeC0Base.V.card ≤ 54 * m_C / k`.
3. `projCompUpdateG`, `projCompBatchG`, `CompLSFState`, `initCompLSF`, `compLSFStepSingle`,
   `compLSFBatch`, `CompLSFInv`, combined `CompLSFState.lsf`, `LSF.Holds`, decremental `F`,
   `wstr` immutability, connected root bound, and `compLSF_mwu_bound` via `lemma_5_5_online`.
-/

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain

@[expose] public section

/-! ## 1. Component subgraphs and size classification -/

/-- Edge set of `G₀` belonging to component `C` (`G₀.tail e ∈ C`). -/
noncomputable def compEdgeSet (G₀ : MGraph) (C : Finset ℕ) : Finset ℕ :=
  open Classical in G₀.E.filter fun e => G₀.tail e ∈ C

/-- Induced subgraph of `G₀` on connected component `C`. -/
noncomputable def compGraph (G₀ : MGraph) (C : Finset ℕ) : MGraph where
  V := C
  E := compEdgeSet G₀ C
  tail := G₀.tail
  head := G₀.head

lemma mem_compEdgeSet_endpoints {G₀ : MGraph} (hG₀ : G₀.IsValid) {C : Finset ℕ}
    (hC : C ∈ components G₀) {e : ℕ} (he : e ∈ compEdgeSet G₀ C) :
    e ∈ G₀.E ∧ G₀.tail e ∈ C ∧ G₀.head e ∈ C := by
  rw [compEdgeSet, Finset.mem_filter] at he
  rcases Finset.mem_image.mp hC with ⟨u, _, rfl⟩
  have htu := (mem_compOf_iff.mp he.2).2
  have he_conn : G₀.Connected (G₀.tail e) (G₀.head e) := connected_of_edge he.1
  have hhead : G₀.head e ∈ compOf G₀ u :=
    mem_compOf_iff.mpr ⟨(hG₀ e he.1).2, connected_trans htu he_conn⟩
  exact ⟨he.1, he.2, hhead⟩

lemma compGraph_isValid {G₀ : MGraph} (hG₀ : G₀.IsValid) {C : Finset ℕ}
    (hC : C ∈ components G₀) : (compGraph G₀ C).IsValid := fun e he => by
  have h := mem_compEdgeSet_endpoints hG₀ hC he
  exact ⟨h.2.1, h.2.2⟩

lemma compGraph_nonempty {G₀ : MGraph} {C : Finset ℕ} (hC : C ∈ components G₀) :
    (compGraph G₀ C).V.Nonempty := by
  rcases Finset.mem_image.mp hC with ⟨u, hu, rfl⟩
  exact ⟨u, self_mem_compOf hu⟩

lemma compGraph_n_le {G₀ : MGraph} {C : Finset ℕ} (hC : C ∈ components G₀) :
    (compGraph G₀ C).n ≤ G₀.n := by
  rcases Finset.mem_image.mp hC with ⟨u, _, rfl⟩
  exact Finset.card_le_card fun v hv => (mem_compOf_iff.mp hv).1

lemma compGraph_m_le {G₀ : MGraph} {C : Finset ℕ} :
    (compGraph G₀ C).m ≤ G₀.m :=
  Finset.card_le_card (Finset.filter_subset _ _)

lemma compGraph_maxDeg_le {G₀ : MGraph} {C : Finset ℕ} (hC : C ∈ components G₀) :
    (compGraph G₀ C).maxDeg ≤ G₀.maxDeg := by
  unfold MGraph.maxDeg
  rw [Finset.sup_le_iff]
  intro v hv
  have hvG : v ∈ G₀.V := by
    rcases Finset.mem_image.mp hC with ⟨u, _, rfl⟩
    exact (mem_compOf_iff.mp hv).1
  have hdeg : (compGraph G₀ C).deg v ≤ G₀.deg v := by
    unfold MGraph.deg
    exact add_le_add
      (Finset.card_le_card fun e he => by
        rw [Finset.mem_filter] at he ⊢; exact ⟨(Finset.mem_filter.mp he.1).1, he.2⟩)
      (Finset.card_le_card fun e he => by
        rw [Finset.mem_filter] at he ⊢; exact ⟨(Finset.mem_filter.mp he.1).1, he.2⟩)
  exact le_trans hdeg (Finset.le_sup (f := G₀.deg) hvG)

lemma compGraph_connected {G₀ : MGraph} (hG₀ : G₀.IsValid) {C : Finset ℕ} (hC : C ∈ components G₀) :
    ∀ u ∈ (compGraph G₀ C).V, ∀ v ∈ (compGraph G₀ C).V, (compGraph G₀ C).Connected u v := by
  rcases Finset.mem_image.mp hC with ⟨w, _, rfl⟩
  intro u hu v hv
  have hcu : G₀.Connected w u := (mem_compOf_iff.mp hu).2
  have hcv : G₀.Connected w v := (mem_compOf_iff.mp hv).2
  obtain ⟨P, hP⟩ := connected_trans (connected_symm hcu) hcv
  refine ⟨P, ?_⟩
  have hwalk : ∀ a b Q, G₀.IsWalk a b Q → G₀.Connected w a →
      (compGraph G₀ (compOf G₀ w)).IsWalk a b Q := by
    intro a b Q hQ
    induction hQ with
    | nil x => intro _; exact .nil x
    | @cons x y z rest hzE hsrc _ ih =>
      intro hwa
      rcases z with ⟨e, b⟩
      have hsrcV : G₀.src (e, b) ∈ G₀.V := by
        cases b <;> simp [MGraph.src, (hG₀ e hzE).1, (hG₀ e hzE).2]
      have hsrcC : G₀.src (e, b) ∈ compOf G₀ w :=
        mem_compOf_iff.mpr ⟨hsrcV, hsrc ▸ hwa⟩
      have heC : e ∈ compEdgeSet G₀ (compOf G₀ w) := by
        rw [compEdgeSet, Finset.mem_filter]
        refine ⟨hzE, ?_⟩
        cases b
        · exact mem_compOf_iff.mpr ⟨(hG₀ e hzE).1,
            connected_trans (mem_compOf_iff.mp hsrcC).2 (connected_symm (connected_of_edge hzE))⟩
        · exact hsrcC
      have hwdst : G₀.Connected w (G₀.dst (e, b)) := by
        cases b
        · simpa [MGraph.dst, MGraph.src] using
            connected_trans (mem_compOf_iff.mp hsrcC).2 (connected_symm (connected_of_edge hzE))
        · simpa [MGraph.dst, MGraph.src] using
            connected_trans (mem_compOf_iff.mp hsrcC).2 (connected_of_edge hzE)
      exact .cons heC hsrc (ih hwdst)
  exact hwalk u v P hP hcu

lemma comp_walk_exit {G : MGraph} {S : Finset ℕ} {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : G.IsWalk u v P) (hu : u ∈ S) (hv : v ∉ S) :
    ∃ e ∈ G.E, (G.tail e ∈ S ∧ G.head e ∉ S) ∨ (G.head e ∈ S ∧ G.tail e ∉ S) := by
  induction hW with
  | nil _ => exact absurd hu hv
  | @cons _ _ x₀ _ hxE hsrc _ ih =>
    by_cases hdst : G.dst x₀ ∈ S
    · exact ih hdst hv
    · rcases x₀ with ⟨e, _ | _⟩
      · simp only [MGraph.src, Bool.false_eq_true, ↓reduceIte] at hsrc
        simp only [MGraph.dst, Bool.false_eq_true, ↓reduceIte] at hdst
        exact ⟨e, hxE, Or.inr ⟨hsrc ▸ hu, hdst⟩⟩
      · simp only [MGraph.src, ↓reduceIte] at hsrc
        simp only [MGraph.dst, ↓reduceIte] at hdst
        exact ⟨e, hxE, Or.inl ⟨hsrc ▸ hu, hdst⟩⟩

private lemma comp_connected_n_le_m_add_one {G : MGraph} (hG : G.IsValid)
    (hConn : ∀ u ∈ G.V, ∀ v ∈ G.V, G.Connected u v) : G.n ≤ G.m + 1 := by
  by_cases hV : G.V.Nonempty
  · obtain ⟨r, hr⟩ := hV
    have hstep : ∀ k : ℕ, k + 1 ≤ G.V.card →
        ∃ (S F : Finset ℕ), S ⊆ G.V ∧ F ⊆ G.E ∧ r ∈ S ∧ S.card = k + 1 ∧ F.card = k ∧
          ∀ e ∈ F, G.tail e ∈ S ∧ G.head e ∈ S := by
      intro k
      induction k with
      | zero =>
        intro _
        exact ⟨{r}, ∅, Finset.singleton_subset_iff.mpr hr, Finset.empty_subset _,
          Finset.mem_singleton_self r, Finset.card_singleton r, Finset.card_empty,
          fun e he => absurd he (Finset.notMem_empty e)⟩
      | succ k ih =>
        intro hk1
        obtain ⟨S, F, hSV, hFE, hrS, hScard, hFcard, hFends⟩ := ih (Nat.le_of_succ_le hk1)
        obtain ⟨w, hwV, hwS⟩ : ∃ w ∈ G.V, w ∉ S := by
          by_contra hnone
          push Not at hnone
          have := Finset.card_le_card (fun v hv => hnone v hv)
          omega
        obtain ⟨P, hP⟩ := hConn r hr w hwV
        obtain ⟨e, heE, hsplit⟩ := comp_walk_exit hP hrS hwS
        have heEnds := hG e heE
        have he_not_F : e ∉ F := fun heF => by
          have ⟨htS, hhS⟩ := hFends e heF
          rcases hsplit with ⟨_, hnh⟩ | ⟨_, hnt⟩
          · exact hnh hhS
          · exact hnt htS
        rcases hsplit with ⟨htS, hnh⟩ | ⟨hhS, hnt⟩
        · exact ⟨insert (G.head e) S, insert e F,
            Finset.insert_subset heEnds.2 hSV, Finset.insert_subset heE hFE,
            Finset.mem_insert_of_mem hrS,
            by rw [Finset.card_insert_of_notMem hnh, hScard],
            by rw [Finset.card_insert_of_notMem he_not_F, hFcard],
            fun f hf => by
              rcases Finset.mem_insert.mp hf with rfl | hfF
              · exact ⟨Finset.mem_insert_of_mem htS, Finset.mem_insert_self _ _⟩
              · exact ⟨Finset.mem_insert_of_mem (hFends f hfF).1,
                  Finset.mem_insert_of_mem (hFends f hfF).2⟩⟩
        · exact ⟨insert (G.tail e) S, insert e F,
            Finset.insert_subset heEnds.1 hSV, Finset.insert_subset heE hFE,
            Finset.mem_insert_of_mem hrS,
            by rw [Finset.card_insert_of_notMem hnt, hScard],
            by rw [Finset.card_insert_of_notMem he_not_F, hFcard],
            fun f hf => by
              rcases Finset.mem_insert.mp hf with rfl | hfF
              · exact ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem hhS⟩
              · exact ⟨Finset.mem_insert_of_mem (hFends f hfF).1,
                  Finset.mem_insert_of_mem (hFends f hfF).2⟩⟩
    have hpos : 0 < G.V.card := Finset.card_pos.mpr ⟨r, hr⟩
    obtain ⟨_, F, _, hFE, _, _, hFcard, _⟩ := hstep (G.V.card - 1) (by omega)
    have hFm : F.card ≤ G.m := Finset.card_le_card hFE
    change G.V.card ≤ G.m + 1
    omega
  · rw [Finset.not_nonempty_iff_eq_empty] at hV
    change G.V.card ≤ G.m + 1
    rw [hV, Finset.card_empty]
    omega

lemma compGraph_n_le_m_add_one {G₀ : MGraph} (hG₀ : G₀.IsValid) {C : Finset ℕ}
    (hC : C ∈ components G₀) :
    (compGraph G₀ C).n ≤ G₀.m + 1 :=
  le_trans (comp_connected_n_le_m_add_one (compGraph_isValid hG₀ hC) (compGraph_connected hG₀ hC))
    (Nat.add_le_add_right compGraph_m_le 1)

lemma compGraph_n_le_min {G₀ : MGraph} (hG₀ : G₀.IsValid) {C : Finset ℕ}
    (hC : C ∈ components G₀) :
    (compGraph G₀ C).n ≤ min G₀.n (G₀.m + 1) :=
  le_min (compGraph_n_le hC) (compGraph_n_le_m_add_one hG₀ hC)

lemma components_V_pairwiseDisjoint (G₀ : MGraph) :
    Set.PairwiseDisjoint (components G₀ : Set (Finset ℕ)) id := by
  intro C₁ hC₁ C₂ hC₂ hne
  rcases Finset.mem_image.mp hC₁ with ⟨u, _, rfl⟩
  rcases Finset.mem_image.mp hC₂ with ⟨v, _, rfl⟩
  refine compOf_disjoint_of_not_connected ?_
  intro hc
  exact hne (compOf_eq_of_connected hc)

lemma components_biUnion_V (G₀ : MGraph) : (components G₀).biUnion id = G₀.V := by
  ext v
  simp only [Finset.mem_biUnion, id_eq, components, Finset.mem_image]
  constructor
  · rintro ⟨_, ⟨u, _, rfl⟩, hv⟩
    exact (mem_compOf_iff.mp hv).1
  · intro hv
    exact ⟨compOf G₀ v, ⟨v, hv, rfl⟩, self_mem_compOf hv⟩

lemma compEdgeSet_pairwiseDisjoint (G₀ : MGraph) :
    Set.PairwiseDisjoint (components G₀ : Set (Finset ℕ)) (compEdgeSet G₀) := by
  intro C₁ hC₁ C₂ hC₂ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro e he₁ he₂
  rw [compEdgeSet, Finset.mem_filter] at he₁ he₂
  exact Finset.disjoint_left.mp (components_V_pairwiseDisjoint G₀ hC₁ hC₂ hne) he₁.2 he₂.2

lemma components_biUnion_compEdgeSet (G₀ : MGraph) (hG₀ : G₀.IsValid) :
    (components G₀).biUnion (compEdgeSet G₀) = G₀.E := by
  ext e
  simp only [Finset.mem_biUnion, compEdgeSet, Finset.mem_filter]
  constructor
  · rintro ⟨_, _, he, _⟩; exact he
  · intro he
    have ht := (hG₀ e he).1
    exact ⟨compOf G₀ (G₀.tail e), compOf_mem_components ht, he, self_mem_compOf ht⟩

lemma components_sum_m (G₀ : MGraph) (hG₀ : G₀.IsValid) :
    ((components G₀).sum fun C => (compGraph G₀ C).m) = G₀.m := by
  have h1 : (components G₀).biUnion (compEdgeSet G₀) = G₀.E :=
    components_biUnion_compEdgeSet G₀ hG₀
  have h2 := Finset.card_biUnion (compEdgeSet_pairwiseDisjoint G₀)
  change ((components G₀).biUnion (compEdgeSet G₀)).card = _ at h2
  rw [h1] at h2
  exact h2.symm

lemma connected_components_eq {G₀ : MGraph} (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    (hconn : ∀ u ∈ G₀.V, ∀ v ∈ G₀.V, G₀.Connected u v) :
    components G₀ = {G₀.V} ∧ compGraph G₀ G₀.V = G₀ := by
  obtain ⟨r, hr⟩ := hV₀
  have hcomp_eq : compOf G₀ r = G₀.V := by
    ext v
    simp only [mem_compOf_iff]
    exact ⟨And.left, fun hv => ⟨hv, hconn r hr v hv⟩⟩
  have hcomps : components G₀ = {G₀.V} := by
    ext C
    simp only [components, Finset.mem_image, Finset.mem_singleton]
    constructor
    · rintro ⟨u, hu, rfl⟩
      rw [← hcomp_eq]
      exact compOf_eq_of_connected (hconn u hu r hr)
    · rintro rfl
      exact ⟨r, hr, hcomp_eq⟩
  have hgraph : compGraph G₀ G₀.V = G₀ := by
    cases G₀ with
    | mk V E tail head =>
      simp only [compGraph, compEdgeSet, MGraph.mk.injEq, Finset.filter_eq_self, true_and]
      exact ⟨fun e he => (hG₀ e he).1, trivial⟩
  exact ⟨hcomps, hgraph⟩

/-- Large components of `G₀` (`1 ≤ m_C` and `k ≤ 4 * m_C`): initialized immediately into `DynSpanner`. -/
noncomputable def largeComps (k : ℕ) (G₀ : MGraph) : Finset (Finset ℕ) :=
  open Classical in (components G₀).filter fun C =>
    1 ≤ (compGraph G₀ C).m ∧ k ≤ 4 * (compGraph G₀ C).m

/-- Non-isolated tiny components (`1 ≤ m_C` and `4 * m_C < k`): lazy activation only when touched. -/
noncomputable def tinyComps (k : ℕ) (G₀ : MGraph) : Finset (Finset ℕ) :=
  open Classical in (components G₀).filter fun C =>
    1 ≤ (compGraph G₀ C).m ∧ 4 * (compGraph G₀ C).m < k

/-- Edge-free isolated-vertex components (`m_C = 0`). -/
noncomputable def isoComps (G₀ : MGraph) : Finset (Finset ℕ) :=
  open Classical in (components G₀).filter fun C => (compGraph G₀ C).m = 0

lemma comp_classes_partition (k : ℕ) (G₀ : MGraph) :
    largeComps k G₀ ∪ tinyComps k G₀ ∪ isoComps G₀ = components G₀ := by
  ext C
  simp only [largeComps, tinyComps, isoComps, Finset.mem_union, Finset.mem_filter]
  by_cases hC : C ∈ components G₀
  · by_cases hm : (compGraph G₀ C).m = 0
    · simp [hC, hm]
    · by_cases hk : k ≤ 4 * (compGraph G₀ C).m
      · simp [hC, hk, Nat.one_le_iff_ne_zero.mpr hm]
      · have h1 : 1 ≤ (compGraph G₀ C).m := Nat.one_le_iff_ne_zero.mpr hm
        have hlt : 4 * (compGraph G₀ C).m < k := lt_of_not_ge hk
        simp [hC, h1, hk, hlt]
  · simp [hC]

lemma comp_classes_disjoint (k : ℕ) (G₀ : MGraph) :
    Disjoint (largeComps k G₀) (tinyComps k G₀) ∧
    Disjoint (largeComps k G₀) (isoComps G₀) ∧
    Disjoint (tinyComps k G₀) (isoComps G₀) := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [Finset.disjoint_left] <;>
    intro C h1 h2 <;> simp only [largeComps, tinyComps, isoComps, Finset.mem_filter] at h1 h2 <;>
    omega

lemma largeComps_sub {k : ℕ} {G₀ : MGraph} : largeComps k G₀ ⊆ components G₀ :=
  Finset.filter_subset _ _

lemma tinyComps_sub {k : ℕ} {G₀ : MGraph} : tinyComps k G₀ ⊆ components G₀ :=
  Finset.filter_subset _ _

lemma isoComps_sub {G₀ : MGraph} : isoComps G₀ ⊆ components G₀ :=
  Finset.filter_subset _ _

lemma initLSF_small_props_with {lsfInit : LSFInit} {C_lsst : ℝ} {k j : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (hk : 1 ≤ k) {C : Finset ℕ} (hC_mem : C ∈ components G₀)
    (hm_lt : 4 * (compGraph G₀ C).m < k) :
    let G_C := compGraph G₀ C
    let S₀ := lsfInit G_C ℓ₀ k j
    S₀.R.card = 1 ∧
    S₀.W_init.card ≤ 9 ∧
    (initTildeState S₀).C.V.card ≤ 11 ∧
    ∀ e ∈ G_C.E, S₀.RF.root (G_C.tail e) = S₀.RF.root (G_C.head e) := by
  intro G_C S₀
  have hGC_val := compGraph_isValid hG₀ hC_mem
  have hGC_ne := compGraph_nonempty hC_mem
  have hGC_conn := compGraph_connected hG₀ hC_mem
  have hℓC : ∀ e ∈ G_C.E, 0 < ℓ₀ e := fun e he => hℓ₀ e (Finset.filter_subset _ _ he)
  have hk_pos : (0 : ℝ) < (k : ℝ) := by positivity
  obtain ⟨hI₀, _, hG_eq, _, _, _, hCov₀, hR, hW⟩ := hInit G_C ℓ₀ hGC_val hGC_ne hℓC hk
  have hm_real : 4 * (G_C.m : ℝ) < (k : ℝ) := by exact_mod_cast hm_lt
  have hR_le : (S₀.R.card : ℝ) ≤ 1 + 4 * (G_C.m : ℝ) / (k : ℝ) := by
    rw [ite_eq_left hGC_conn] at hR
    exact hR
  have hR_lt2 : (S₀.R.card : ℝ) < 2 := by
    have : 4 * (G_C.m : ℝ) / (k : ℝ) < 1 := (div_lt_one hk_pos).mpr hm_real
    linarith
  have hR_le1 : S₀.R.card ≤ 1 := by
    have : (S₀.R.card : ℝ) < ((2 : ℕ) : ℝ) := by simpa using hR_lt2
    exact Nat.le_of_lt_succ (Nat.cast_lt.mp this)
  have hR_ge1 : 1 ≤ S₀.R.card :=
    Finset.card_pos.mpr ⟨S₀.r₀, subset_upClosure hI₀.hr₀_base |> Finset.mem_union_left _⟩
  have hR_eq : S₀.R.card = 1 := le_antisymm hR_le1 hR_ge1
  have hW_le : (S₀.W_init.card : ℝ) ≤ 6 + 1 + 10 * (G_C.m : ℝ) / (k : ℝ) := by
    rw [ite_eq_left hGC_conn] at hW
    exact hW
  have hW_lt10 : (S₀.W_init.card : ℝ) < 10 := by
    have h4 : 4 * ((G_C.m : ℝ) / (k : ℝ)) < 1 := by
      have := (div_lt_one hk_pos).mpr hm_real
      linarith [show 4 * ((G_C.m : ℝ) / (k : ℝ)) = 4 * (G_C.m : ℝ) / (k : ℝ) from by ring]
    have heq : 10 * (G_C.E.card : ℝ) / (k : ℝ) = 10 * ((G_C.m : ℝ) / (k : ℝ)) := by
      change 10 * (G_C.m : ℝ) / (k : ℝ) = _
      ring
    change (S₀.W_init.card : ℝ) ≤ 6 + 1 + 10 * (G_C.E.card : ℝ) / (k : ℝ) at hW_le
    rw [heq] at hW_le
    linarith [hW_le]
  have hW_le9 : S₀.W_init.card ≤ 9 := by
    have : (S₀.W_init.card : ℝ) < ((10 : ℕ) : ℝ) := by simpa using hW_lt10
    exact Nat.le_of_lt_succ (Nat.cast_lt.mp this)
  have hb₀ : boundary S₀.W_init ⊆ S₀.R := Finset.Subset.trans hI₀.hb_W Finset.subset_union_left
  have hC_card := tildeC0Base_V_card_le (lsfInv_to_RS hI₀) hCov₀ hb₀
    (fun W hW => (hI₀.hW_props W hW).2.2.1)
  have hC_card' : (initTildeState S₀).C.V.card ≤ 2 * S₀.R.card + S₀.W_init.card := hC_card
  have hRoot : ∀ e ∈ G_C.E, S₀.RF.root (G_C.tail e) = S₀.RF.root (G_C.head e) := by
    intro e he
    have hRF₀ := lsfInv_to_RS hI₀
    have ht_R : S₀.RF.root (G_C.tail e) ∈ S₀.R :=
      (rootedForest_root_spec hRF₀ (hG_eq.symm ▸ (hGC_val e he).1)).1
    have hh_R : S₀.RF.root (G_C.head e) ∈ S₀.R :=
      (rootedForest_root_spec hRF₀ (hG_eq.symm ▸ (hGC_val e he).2)).1
    exact Finset.card_le_one.mp hR_le1 _ ht_R _ hh_R
  exact ⟨hR_eq, hW_le9, by omega, hRoot⟩

lemma initLSF_small_props {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {k : ℕ} (hk : 1 ≤ k) {C : Finset ℕ} (hC_mem : C ∈ components G₀)
    (hm_lt : 4 * (compGraph G₀ C).m < k) (j : ℕ) :
    let G_C := compGraph G₀ C
    let S₀ := initLSFOnline oracle C_lsst G_C ℓ₀ k j
    S₀.R.card = 1 ∧
    S₀.W_init.card ≤ 9 ∧
    (initTildeState S₀).C.V.card ≤ 11 ∧
    ∀ e ∈ G_C.E, S₀.RF.root (G_C.tail e) = S₀.RF.root (G_C.head e) :=
  initLSF_small_props_with (initLSFOnline_isValidLSFInitFor hLSST k j) hG₀ hℓ₀ hk hC_mem hm_lt

lemma initLSF_tiny_props {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {k : ℕ} (hk : 1 ≤ k) {C : Finset ℕ} (hC : C ∈ tinyComps k G₀) (j : ℕ) :
    let G_C := compGraph G₀ C
    let S₀ := initLSFOnline oracle C_lsst G_C ℓ₀ k j
    S₀.R.card = 1 ∧
    S₀.W_init.card ≤ 9 ∧
    (initTildeState S₀).C.V.card ≤ 11 ∧
    ∀ e ∈ G_C.E, S₀.RF.root (G_C.tail e) = S₀.RF.root (G_C.head e) :=
  initLSF_small_props hLSST hG₀ hℓ₀ hk (tinyComps_sub hC) (Finset.mem_filter.mp hC).2.2 j

lemma initLSF_large_tildeV_le {oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph} {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {k : ℕ} (hk : 1 ≤ k) {C : Finset ℕ} (hC : C ∈ largeComps k G₀) (j : ℕ) :
    let G_C := compGraph G₀ C
    let S₀ := initLSFOnline oracle C_lsst G_C ℓ₀ k j
    ((initTildeState S₀).C.V.card : ℝ) ≤ 54 * (G_C.m : ℝ) / (k : ℝ) := by
  intro G_C S₀
  have hC_mem : C ∈ components G₀ := largeComps_sub hC
  have hGC_val := compGraph_isValid hG₀ hC_mem
  have hGC_ne := compGraph_nonempty hC_mem
  have hGC_conn := compGraph_connected hG₀ hC_mem
  have hℓC : ∀ e ∈ G_C.E, 0 < ℓ₀ e := fun e he => hℓ₀ e (Finset.filter_subset _ _ he)
  have hw : ∀ e ∈ G_C.E, 0 < mwuWeights oracle C_lsst G_C ℓ₀ k j e :=
    fun e _ => mwuWeights_pos oracle C_lsst G_C ℓ₀ k j e
  have hk_real : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hm_ge : k ≤ 4 * G_C.m := (Finset.mem_filter.mp hC).2.2
  have h1_le : (1 : ℝ) ≤ 4 * ((G_C.m : ℝ) / (k : ℝ)) := by
    have hm_r : (k : ℝ) ≤ 4 * (G_C.m : ℝ) := by exact_mod_cast hm_ge
    have := (one_le_div (by positivity : (0 : ℝ) < k)).mpr hm_r
    linarith [show 4 * ((G_C.m : ℝ) / (k : ℝ)) = 4 * (G_C.m : ℝ) / (k : ℝ) from by ring]
  have hsp := initLSF_spec hLSST hGC_val hGC_ne hℓC hw hk_real
  have hI₀ : LSFInv C_lsst ℓ₀ S₀ := initLSF_inv hLSST hGC_val hGC_ne hℓC hw hk_real
  have hCov₀ : S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E :=
    hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hR_le : (S₀.R.card : ℝ) ≤ 8 * ((G_C.m : ℝ) / (k : ℝ)) := by
    have hR := hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    split_ifs at hR
    have hEqR : 4 * (G_C.E.card : ℝ) / (k : ℝ) = 4 * ((G_C.m : ℝ) / (k : ℝ)) := by
      change 4 * (G_C.m : ℝ) / (k : ℝ) = _; ring
    change (S₀.R.card : ℝ) ≤ 1 + 4 * (G_C.E.card : ℝ) / (k : ℝ) at hR
    rw [hEqR] at hR
    linarith
  have hW_le : (S₀.W_init.card : ℝ) ≤ 38 * ((G_C.m : ℝ) / (k : ℝ)) := by
    have hW := hsp.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
    split_ifs at hW
    have hEqW : 10 * (G_C.E.card : ℝ) / (k : ℝ) = 10 * ((G_C.m : ℝ) / (k : ℝ)) := by
      change 10 * (G_C.m : ℝ) / (k : ℝ) = _; ring
    change (S₀.W_init.card : ℝ) ≤ 6 + 1 + 10 * (G_C.E.card : ℝ) / (k : ℝ) at hW
    rw [hEqW] at hW
    linarith
  have hb₀ : boundary S₀.W_init ⊆ S₀.R := Finset.Subset.trans hI₀.hb_W Finset.subset_union_left
  have hC_card : ((initTildeState S₀).C.V.card : ℝ) ≤ 2 * (S₀.R.card : ℝ) + (S₀.W_init.card : ℝ) := by
    change ((tildeC0Base S₀).V.card : ℝ) ≤ 2 * (S₀.R.card : ℝ) + (S₀.W_init.card : ℝ)
    exact_mod_cast tildeC0Base_V_card_le (lsfInv_to_RS hI₀) hCov₀ hb₀
      (fun W hW => (hI₀.hW_props W hW).2.2.1)
  have hsum_eq : 54 * ((G_C.m : ℝ) / (k : ℝ)) = 54 * (G_C.m : ℝ) / (k : ℝ) := by ring
  linarith

/-! ## 2. Component update projection and dynamic state `CompLSFState` -/

/-- Project one global update `u` on `G_glob` onto a component graph `G_C`. -/
noncomputable def projCompUpdateG (G_glob G_C : MGraph) (u : Update) : List Update :=
  open Classical in
  match u with
  | .delete e => if e ∈ G_C.E then [.delete e] else []
  | .insert e a b =>
    if a ∈ G_C.V ∧ b ∈ G_C.V then [.insert e a b]
    else if a ∈ G_C.V then [.insert e a a, .delete e]
    else if b ∈ G_C.V then [.insert e b b, .delete e]
    else []
  | .split v v' St Sh =>
    if v ∈ G_C.V then
      [.split v v'
        (G_C.E.filter fun e => e ∈ St ∧ G_C.tail e = v ∧ G_glob.tail e = v)
        (G_C.E.filter fun e => e ∈ Sh ∧ G_C.head e = v ∧ G_glob.head e = v)]
    else []

/-- Project an update batch `U` on `G_glob` onto `G_C`, tracking intermediate `G_glob` and `G_C`. -/
noncomputable def projCompBatchG (G_glob G_C : MGraph) : List Update → List Update
  | [] => []
  | u :: rest =>
    let U_u := projCompUpdateG G_glob G_C u
    U_u ++ projCompBatchG (G_glob.applyUpdate u) (G_C.applyBatch U_u) rest

lemma projCompBatchG_append (G_glob G_C : MGraph) (U₁ U₂ : List Update) :
    projCompBatchG G_glob G_C (U₁ ++ U₂) =
      projCompBatchG G_glob G_C U₁ ++
        projCompBatchG (G_glob.applyBatch U₁)
          (G_C.applyBatch (projCompBatchG G_glob G_C U₁)) U₂ := by
  induction U₁ generalizing G_glob G_C with
  | nil => simp [projCompBatchG, MGraph.applyBatch]
  | cons u rest ih =>
    simp only [List.cons_append, projCompBatchG, List.append_assoc]
    congr 1
    change projCompBatchG (G_glob.applyUpdate u)
        (G_C.applyBatch (projCompUpdateG G_glob G_C u)) (rest ++ U₂) =
      projCompBatchG (G_glob.applyUpdate u)
          (G_C.applyBatch (projCompUpdateG G_glob G_C u)) rest ++
        projCompBatchG ((G_glob.applyUpdate u).applyBatch rest)
          (G_C.applyBatch (projCompUpdateG G_glob G_C u ++
            projCompBatchG (G_glob.applyUpdate u)
              (G_C.applyBatch (projCompUpdateG G_glob G_C u)) rest)) U₂
    rw [ih (G_glob.applyUpdate u) (G_C.applyBatch (projCompUpdateG G_glob G_C u)),
      applyBatch_append]

lemma applyLSFBatch_G_of_valid {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState} {U : List Update}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) (hBU : S.G.BatchIsValid U) :
    (applyLSFBatch S U).G = S.G.applyBatch U :=
  (applyLSFBatch_inv_with U hI hBU).2.1

/-- The least vertex of a set, and `0` for the empty set. -/
def compKey (C : Finset ℕ) : ℕ := if h : C.Nonempty then C.min' h else 0

/-- Index of component `C`: the position of its least vertex in the sorted list of the least
vertices of all components. -/
noncomputable def compIdx (G₀ : MGraph) (C : Finset ℕ) : ℕ :=
  (((components G₀).image compKey).sort (· ≤ ·)).idxOf (compKey C)

private lemma compKey_mem {G₀ : MGraph} {C : Finset ℕ} (hC : C ∈ components G₀) :
    compKey C ∈ C := by
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hC
  have hne : (compOf G₀ u).Nonempty := ⟨u, self_mem_compOf hu⟩
  simpa only [compKey, hne, ↓reduceDIte] using Finset.min'_mem _ hne

lemma compIdx_inj {G₀ : MGraph} {C₁ C₂ : Finset ℕ}
    (h₁ : C₁ ∈ components G₀) (h₂ : C₂ ∈ components G₀) (heq : compIdx G₀ C₁ = compIdx G₀ C₂) :
    C₁ = C₂ := by
  have hm : compKey C₁ ∈ ((components G₀).image compKey).sort (· ≤ ·) :=
    (Finset.mem_sort _).mpr (Finset.mem_image_of_mem _ h₁)
  have hk : compKey C₁ = compKey C₂ := (List.idxOf_inj hm).mp heq
  obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp h₁
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp h₂
  have hw₁ := mem_compOf_iff.mp (compKey_mem h₁)
  have hw₂ := mem_compOf_iff.mp (hk ▸ compKey_mem h₂)
  exact (compOf_eq_iff hv).mpr (connected_trans hw₁.2 (connected_symm hw₂.2))

/-- Injectively relabel any non-component bridge edges in `(compSt C).T_cur.E` while leaving every
edge in `(compGraph G₀ C).E` (including all `RF.F.E`) untouched. -/
noncomputable def encTEdge (G₀ : MGraph) (C : Finset ℕ) (f : ℕ) : ℕ :=
  open Classical in
  if f ∈ compEdgeSet G₀ C then f else (G₀.E.sup id + 1) + Nat.pair (compIdx G₀ C) f

lemma encTEdge_eq_self {G₀ : MGraph} {C : Finset ℕ} {f : ℕ} (hf : f ∈ compEdgeSet G₀ C) :
    encTEdge G₀ C f = f := by
  classical
  simp [encTEdge, hf]

lemma encTEdge_inj {G₀ : MGraph} {C₁ C₂ : Finset ℕ}
    (hC₁ : C₁ ∈ components G₀) (hC₂ : C₂ ∈ components G₀) {f₁ f₂ : ℕ}
    (heq : encTEdge G₀ C₁ f₁ = encTEdge G₀ C₂ f₂) : C₁ = C₂ ∧ f₁ = f₂ := by
  classical
  unfold encTEdge at heq
  by_cases h1 : f₁ ∈ compEdgeSet G₀ C₁ <;> by_cases h2 : f₂ ∈ compEdgeSet G₀ C₂
  · simp only [h1, h2, ↓reduceIte] at heq
    have hdisj := compEdgeSet_pairwiseDisjoint G₀ hC₁ hC₂
    by_cases hC : C₁ = C₂
    · exact ⟨hC, heq⟩
    · exfalso
      exact Finset.disjoint_left.mp (hdisj hC) h1 (heq ▸ h2)
  · simp only [h1, h2, ↓reduceIte] at heq
    have hle := Finset.le_sup (f := id) (Finset.mem_filter.mp h1).1
    dsimp only [id_eq] at hle
    omega
  · simp only [h1, h2, ↓reduceIte] at heq
    have hle := Finset.le_sup (f := id) (Finset.mem_filter.mp h2).1
    dsimp only [id_eq] at hle
    omega
  · simp only [h1, h2, ↓reduceIte] at heq
    have hpair : Nat.pair (compIdx G₀ C₁) f₁ = Nat.pair (compIdx G₀ C₂) f₂ := by omega
    have hp := Nat.pair_eq_pair.mp hpair
    exact ⟨compIdx_inj hC₁ hC₂ hp.1, hp.2⟩

/-- Component-wise dynamic LSF state on nonempty valid graph `G₀`. -/
structure CompLSFState where
  G₀ : MGraph
  G : MGraph
  k : ℕ
  compSt : Finset ℕ → LSFState
  crossEdges : Finset ℕ
  insertedGlobal : Finset ℕ
  wstrGlobal : ℕ → ℝ

/-- Disjoint-union forest `T` of a `CompLSFState`: the surviving original tree edges
(those in `cs.G.E \ cs.insertedGlobal`) with their current endpoints in `cs.G`. -/
noncomputable def CompLSFState.T (cs : CompLSFState) : MGraph :=
  open Classical in
  { V := cs.G.V
    E := ((components cs.G₀).biUnion fun C => ((cs.compSt C).T_cur.E.image (encTEdge cs.G₀ C))) ∩
      (cs.G.E \ cs.insertedGlobal)
    tail := cs.G.tail
    head := cs.G.head }

/-- Disjoint-union rooted spanning forest `RF` of a `CompLSFState`. -/
noncomputable def CompLSFState.RF (cs : CompLSFState) : RootedForest :=
  open Classical in
  { F := { V := cs.G.V
           E := (components cs.G₀).biUnion fun C => (cs.compSt C).RF.F.E
           tail := cs.G.tail
           head := cs.G.head }
    R := (components cs.G₀).biUnion fun C => (cs.compSt C).R }

/-- Exposed `LSF` triple of `CompLSFState`. -/
noncomputable def CompLSFState.lsf (cs : CompLSFState) : LSF :=
  ⟨cs.T, cs.RF, cs.wstrGlobal⟩

/-- Initialize `CompLSFState` on `(G₀, ℓ₀)` using an arbitrary LSF initializer `lsfInit`, masking
edge lengths outside `G₀.E` via `safeLen`. -/
noncomputable def initCompLSFWith (lsfInit : LSFInit)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k j : ℕ) : CompLSFState :=
  open Classical in
  let compSt : Finset ℕ → LSFState := fun C =>
    lsfInit (compGraph G₀ C) (safeLen G₀ ℓ₀) k j
  let wstr0 : ℕ → ℝ := fun e =>
    if h : ∃ C ∈ components G₀, e ∈ compEdgeSet G₀ C then
      (compSt h.choose).wstr e
    else 1
  { G₀ := G₀
    G := G₀
    k := k
    compSt := compSt
    crossEdges := ∅
    insertedGlobal := ∅
    wstrGlobal := wstr0 }

/-- Initialize `CompLSFState` on `(G₀, ℓ₀)`, masking edge lengths outside `G₀.E` via `safeLen`. -/
noncomputable def initCompLSF
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) (ℓ₀ : ℕ → ℝ) (k j : ℕ) : CompLSFState :=
  initCompLSFWith (initLSFOnline oracle C_lsst) G₀ ℓ₀ k j

lemma safeLen_eq_of_eq_on_E {G : MGraph} {ℓ₀ ℓ₁ : ℕ → ℝ} (h : ∀ a ∈ G.E, ℓ₀ a = ℓ₁ a) :
    safeLen G ℓ₀ = safeLen G ℓ₁ := by
  classical
  funext e
  unfold safeLen
  split_ifs with he
  · exact h e he
  · rfl

lemma safeLen_zeroExtension (G : MGraph) (ℓ₀ : ℕ → ℝ) :
    safeLen G (fun a => if a ∈ G.E then ℓ₀ a else 0) = safeLen G ℓ₀ :=
  safeLen_eq_of_eq_on_E fun a ha => by simp [ha]

lemma initCompLSFWith_eq_of_eq_on_E (lsfInit : LSFInit)
    (G₀ : MGraph) {ℓ₀ ℓ₁ : ℕ → ℝ} (h : ∀ a ∈ G₀.E, ℓ₀ a = ℓ₁ a) (k j : ℕ) :
    initCompLSFWith lsfInit G₀ ℓ₀ k j = initCompLSFWith lsfInit G₀ ℓ₁ k j := by
  unfold initCompLSFWith
  rw [safeLen_eq_of_eq_on_E h]

lemma initCompLSF_eq_of_eq_on_E
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (G₀ : MGraph) {ℓ₀ ℓ₁ : ℕ → ℝ} (h : ∀ a ∈ G₀.E, ℓ₀ a = ℓ₁ a) (k j : ℕ) :
    initCompLSF oracle C_lsst G₀ ℓ₀ k j = initCompLSF oracle C_lsst G₀ ℓ₁ k j :=
  initCompLSFWith_eq_of_eq_on_E (initLSFOnline oracle C_lsst) G₀ h k j

lemma initCompLSFWith_compSt_basic {lsfInit : LSFInit} {C_lsst : ℝ} {k j : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    (hk : 1 ≤ k) {C : Finset ℕ} (hC : C ∈ components G₀) :
    let S₀ := (initCompLSFWith lsfInit G₀ ℓ₀ k j).compSt C
    S₀.G₀ = compGraph G₀ C ∧
    S₀.G = compGraph G₀ C ∧
    S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E := by
  set ℓs := safeLen G₀ ℓ₀
  have hℓC : ∀ e ∈ (compGraph G₀ C).E, 0 < ℓs e := fun e he => by
    have heG : e ∈ G₀.E := Finset.filter_subset _ _ he
    rw [show ℓs e = ℓ₀ e from safeLen_eq_of_mem ℓ₀ heG]
    exact hℓ₀ e heG
  have hsp := hInit (compGraph G₀ C) ℓs (compGraph_isValid hG₀ hC) (compGraph_nonempty hC) hℓC hk
  exact ⟨hsp.2.1, hsp.2.2.1, hsp.2.2.2.2.2.2.1⟩

lemma initCompLSF_compSt_basic
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) {C_lsst : ℝ}
    (hLSST : HasLSSTSpec oracle C_lsst)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {k : ℕ} (hk : 1 ≤ k) (j : ℕ) {C : Finset ℕ} (hC : C ∈ components G₀) :
    let S₀ := (initCompLSF oracle C_lsst G₀ ℓ₀ k j).compSt C
    S₀.G₀ = compGraph G₀ C ∧
    S₀.G = compGraph G₀ C ∧
    S₀.W_init.biUnion (inducedEdges S₀.RF.F) = S₀.RF.F.E :=
  initCompLSFWith_compSt_basic (initLSFOnline_isValidLSFInitFor hLSST k j) hG₀ hℓ₀ hk hC

/-- Step `CompLSFState` by one valid update `u` on `cs.G`. -/
noncomputable def compLSFStepSingle (cs : CompLSFState) (u : Update) : CompLSFState :=
  open Classical in
  let compSt' : Finset ℕ → LSFState := fun C =>
    applyLSFBatch (cs.compSt C) (projCompUpdateG cs.G (cs.compSt C).G u)
  let cross' : Finset ℕ :=
    match u with
    | .delete e => cs.crossEdges.erase e
    | .insert e a b =>
      if ∃ C ∈ components cs.G₀, a ∈ (cs.compSt C).G.V ∧ b ∈ (cs.compSt C).G.V
      then cs.crossEdges
      else insert e cs.crossEdges
    | .split _ _ _ _ => cs.crossEdges
  let ins' := updateInserted cs.insertedGlobal u
  let wstr' : ℕ → ℝ :=
    match u with
    | .insert e _ _ => Function.update cs.wstrGlobal e 1
    | _ => cs.wstrGlobal
  { cs with
    G := cs.G.applyUpdate u
    compSt := compSt'
    crossEdges := cross'
    insertedGlobal := ins'
    wstrGlobal := wstr' }

/-- Step `CompLSFState` by an update batch `U` on `cs.G`. -/
noncomputable def compLSFBatch (cs : CompLSFState) (U : List Update) : CompLSFState :=
  U.foldl compLSFStepSingle cs

lemma compLSFBatch_G (cs : CompLSFState) (U : List Update) :
    (compLSFBatch cs U).G = cs.G.applyBatch U := by
  induction U generalizing cs with
  | nil => rfl
  | cons u rest ih =>
    change (compLSFBatch (compLSFStepSingle cs u) rest).G = (cs.G.applyUpdate u).applyBatch rest
    exact ih (compLSFStepSingle cs u)

lemma compLSFBatch_G₀ (cs : CompLSFState) (U : List Update) :
    (compLSFBatch cs U).G₀ = cs.G₀ := by
  induction U generalizing cs with
  | nil => rfl
  | cons u rest ih => exact ih (compLSFStepSingle cs u)

lemma compLSFBatch_k (cs : CompLSFState) (U : List Update) :
    (compLSFBatch cs U).k = cs.k := by
  induction U generalizing cs with
  | nil => rfl
  | cons u rest ih => exact ih (compLSFStepSingle cs u)

lemma compLSFBatch_insertedGlobal (cs : CompLSFState) (U : List Update) :
    (compLSFBatch cs U).insertedGlobal = U.foldl updateInserted cs.insertedGlobal := by
  induction U generalizing cs with
  | nil => rfl
  | cons u rest ih =>
    change (compLSFBatch (compLSFStepSingle cs u) rest).insertedGlobal = _
    exact ih (compLSFStepSingle cs u)

lemma compLSFStepSingle_wstr_of_not_inserts (cs : CompLSFState) {u : Update} {e : ℕ}
    (hni : ¬ u.Inserts e) : (compLSFStepSingle cs u).wstrGlobal e = cs.wstrGlobal e := by
  cases u with
  | delete _ => rfl
  | split _ _ _ _ => rfl
  | insert e₀ a b =>
    have hne : e ≠ e₀ := fun h => hni (by simpa [Update.Inserts] using h.symm)
    simp [compLSFStepSingle, Function.update_of_ne hne]

lemma compLSFStepSingle_wstr_of_inserts (cs : CompLSFState) {u : Update} {e : ℕ}
    (hi : u.Inserts e) : (compLSFStepSingle cs u).wstrGlobal e = 1 := by
  cases u with
  | delete _ => simp [Update.Inserts] at hi
  | split _ _ _ _ => simp [Update.Inserts] at hi
  | insert e₀ _ _ =>
    simp only [Update.Inserts] at hi
    subst hi
    simp [compLSFStepSingle]

lemma compLSFBatch_wstr_of_not_inserts (cs : CompLSFState) (U : List Update) {e : ℕ}
    (hni : ∀ u ∈ U, ¬ u.Inserts e) :
    (compLSFBatch cs U).wstrGlobal e = cs.wstrGlobal e := by
  induction U generalizing cs with
  | nil => rfl
  | cons u rest ih =>
    change (compLSFBatch (compLSFStepSingle cs u) rest).wstrGlobal e = cs.wstrGlobal e
    rw [ih _ (fun x hx => hni x (List.mem_cons_of_mem _ hx))]
    exact compLSFStepSingle_wstr_of_not_inserts cs (hni u List.mem_cons_self)

end

end MinCostFlow.SparseCore
