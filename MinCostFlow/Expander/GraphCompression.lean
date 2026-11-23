module

public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Spanner.ToolContracts
public import MinCostFlow.Expander.WordRAMHelpers

import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Active-Vertex Compression Math, List Swaps, and Max-Heap Invariants

Pure mathematical lemmas supporting `ActiveSortProg`:
1. Graph compression onto sorted active vertices (`ActVertsSpec`, `compressGraph`,
   `liftRawComps`, `decomposeProp_of_compressed`).
2. `MemFrame` memory framing helpers and `tab` array lemmas.
3. `listSwap` permutation/indexing lemmas and `IsHeapRange` / `SiftInv` max-heap invariants.
-/

@[expose] public section

namespace MinCostFlow.Expander

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 1. Pure Active-Vertex Compression and `DecomposeOutput` Lifting -/

/-- Compress edge list `es` by mapping each endpoint `u` to its index `actVerts.idxOf u`. -/
def compressEdges (actVerts : List ℕ) (es : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  es.map fun e => (actVerts.idxOf e.1, actVerts.idxOf e.2)

/-- Compressed graph `G_act` on vertices `0, …, actVerts.length - 1`. -/
def compressGraph (actVerts : List ℕ) (G : Cited.Graph) : Cited.Graph :=
  ⟨actVerts.length, compressEdges actVerts G.edges⟩

/-- Lift component records from compressed indices `0..actVerts.length - 1` back to `G`. -/
def liftRawComps (actVerts : List ℕ) (rawComps : List (ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  rawComps.map fun c => (c.1, c.2.map fun i => actVerts.getD i 0)

/-- Specification of a sorted deduplicated active-vertex list covering all edge endpoints of `G`. -/
structure ActVertsSpec (G : Cited.Graph) (actVerts : List ℕ) : Prop where
  strict : actVerts.Pairwise (· < ·)
  lt_n : ∀ u ∈ actVerts, u < G.n
  covers : ∀ e ∈ G.edges, e.1 ∈ actVerts ∧ e.2 ∈ actVerts

lemma ActVertsSpec.nodup {G : Cited.Graph} {actVerts : List ℕ}
    (h : ActVertsSpec G actVerts) : actVerts.Nodup :=
  h.strict.imp fun hlt => ne_of_lt hlt

lemma ActVertsSpec.length_le_n {G : Cited.Graph} {actVerts : List ℕ}
    (h : ActVertsSpec G actVerts) : actVerts.length ≤ G.n := by
  have hsub : actVerts.toFinset ⊆ Finset.range G.n := fun u hu =>
    Finset.mem_range.mpr (h.lt_n u (List.mem_toFinset.mp hu))
  calc
    actVerts.length = actVerts.toFinset.card := (List.toFinset_card_of_nodup h.nodup).symm
    _ ≤ (Finset.range G.n).card := Finset.card_le_card hsub
    _ = G.n := Finset.card_range G.n

lemma getD_lt_of_lt {l : List ℕ} {i n : ℕ} (hi : i < l.length) (hbound : ∀ u ∈ l, u < n) :
    l.getD i 0 < n := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact hbound l[i] (List.getElem_mem hi)

lemma pairwise_lt_getElem_lt {l : List ℕ} (hs : l.Pairwise (· < ·))
    {i j : ℕ} (hij : i < j) (hj : j < l.length) : l[i]'(Nat.lt_trans hij hj) < l[j] :=
  (List.pairwise_iff_getElem.mp hs) i j (Nat.lt_trans hij hj) hj hij

lemma pairwise_lt_getD_lt {l : List ℕ} (hs : l.Pairwise (· < ·))
    {i j : ℕ} (hij : i < j) (hj : j < l.length) : l.getD i 0 < l.getD j 0 := by
  have hi : i < l.length := Nat.lt_trans hij hj
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    Option.getD_some]
  exact pairwise_lt_getElem_lt hs hij hj

lemma pairwise_lt_getD_inj {l : List ℕ} (hs : l.Pairwise (· < ·))
    {i j : ℕ} (hi : i < l.length) (hj : j < l.length)
    (heq : l.getD i 0 = l.getD j 0) : i = j := by
  rcases lt_trichotomy i j with h | rfl | h
  · exact absurd heq (ne_of_lt (pairwise_lt_getD_lt hs h hj))
  · rfl
  · exact absurd heq.symm (ne_of_lt (pairwise_lt_getD_lt hs h hi))

lemma ActVertsSpec.idxOf_lt {G : Cited.Graph} {actVerts : List ℕ}
    (_h : ActVertsSpec G actVerts) {u : ℕ} (hu : u ∈ actVerts) :
    actVerts.idxOf u < actVerts.length :=
  List.idxOf_lt_length_of_mem hu

lemma ActVertsSpec.getD_idxOf {G : Cited.Graph} {actVerts : List ℕ}
    (h : ActVertsSpec G actVerts) {u : ℕ} (hu : u ∈ actVerts) :
    actVerts.getD (actVerts.idxOf u) 0 = u := by
  have hlt := h.idxOf_lt hu
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hlt, Option.getD_some]
  exact List.getElem_idxOf hlt

lemma ActVertsSpec.idxOf_getD {G : Cited.Graph} {actVerts : List ℕ}
    (h : ActVertsSpec G actVerts) {i : ℕ} (hi : i < actVerts.length) :
    actVerts.idxOf (actVerts.getD i 0) = i := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some]
  exact h.nodup.idxOf_getElem i hi

lemma compressGraph_m (actVerts : List ℕ) (G : Cited.Graph) :
    (compressGraph actVerts G).m = G.m := by
  simp [compressGraph, compressEdges, Cited.Graph.m]

lemma compressGraph_isValid {G : Cited.Graph} {actVerts : List ℕ}
    (h : ActVertsSpec G actVerts) : (compressGraph actVerts G).IsValid := by
  intro e he
  simp only [compressGraph, compressEdges, List.mem_map] at he
  rcases he with ⟨e₀, he₀, rfl⟩
  have hc := h.covers e₀ he₀
  exact ⟨h.idxOf_lt hc.1, h.idxOf_lt hc.2⟩

lemma compressGraph_isLoopless {G : Cited.Graph} {actVerts : List ℕ}
    (h : ActVertsSpec G actVerts) (hL : G.IsLoopless) :
    (compressGraph actVerts G).IsLoopless := by
  intro e he heq
  simp only [compressGraph, compressEdges, List.mem_map] at he
  rcases he with ⟨e₀, he₀, rfl⟩
  dsimp only at heq
  have hc := h.covers e₀ he₀
  have h1 := h.getD_idxOf hc.1
  have h2 := h.getD_idxOf hc.2
  rw [heq, h2] at h1
  exact hL e₀ he₀ h1.symm

lemma liftRawComps_pairwise {actVerts : List ℕ} {rawComps : List (ℕ × List ℕ)}
    (hp : rawComps.Pairwise (fun a b => a.1 ≤ b.1)) :
    (liftRawComps actVerts rawComps).Pairwise (fun a b => a.1 ≤ b.1) := by
  simp only [liftRawComps]
  exact hp.map _ (fun _ _ h => h)

private lemma pairwise_lt_map_getD {actVerts : List ℕ} (hstrict : actVerts.Pairwise (· < ·)) :
    ∀ {xs : List ℕ}, xs.Pairwise (· < ·) → (∀ i ∈ xs, i < actVerts.length) →
      (xs.map fun i => actVerts.getD i 0).Pairwise (· < ·)
  | [], _, _ => List.Pairwise.nil
  | _ :: _, hp, hlt => by
    rw [List.pairwise_cons] at hp
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, pairwise_lt_map_getD hstrict hp.2 fun y hy =>
      hlt y (List.mem_cons_of_mem _ hy)⟩
    intro u hu
    rcases List.mem_map.mp hu with ⟨y, hy, rfl⟩
    exact pairwise_lt_getD_lt hstrict (hp.1 y hy) (hlt y (List.mem_cons_of_mem _ hy))

lemma liftRawComps_entry_props {G : Cited.Graph} {actVerts : List ℕ}
    (hact : ActVertsSpec G actVerts) {d_ℓ : ℕ} {rawComps : List (ℕ × List ℕ)}
    (hrec : ∀ c ∈ rawComps, 1 ≤ c.1 ∧ c.1 ≤ d_ℓ ∧ c.2.Pairwise (· < ·) ∧ 2 ≤ c.2.length)
    (hverts : ∀ c ∈ rawComps, ∀ i ∈ c.2, i < actVerts.length) :
    ∀ c ∈ liftRawComps actVerts rawComps,
      1 ≤ c.1 ∧ c.1 ≤ d_ℓ ∧ c.2.Pairwise (· < ·) ∧ 2 ≤ c.2.length := by
  intro c hc
  simp only [liftRawComps, List.mem_map] at hc
  rcases hc with ⟨c₀, hc₀, rfl⟩
  have h₀ := hrec c₀ hc₀
  exact ⟨h₀.1, h₀.2.1, pairwise_lt_map_getD hact.strict h₀.2.2.1 (hverts c₀ hc₀), by simpa using h₀.2.2.2⟩

private lemma list_filter_map_length {α β : Type*} (f : α → β) (l : List α)
    (p : β → Bool) (q : α → Bool) (hpq : ∀ x ∈ l, p (f x) = q x) :
    (l.filter q).length = ((l.map f).filter p).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.map_cons, List.filter_cons]
    have hx := hpq x List.mem_cons_self
    have hxs := ih fun y hy => hpq y (List.mem_cons_of_mem _ hy)
    rw [hx]
    cases hqx : q x <;> simp [hxs]

private lemma pairwise_disjoint_image {f : ℕ → ℕ} {n : ℕ}
    (hinj : ∀ i j, i < n → j < n → f i = f j → i = j) :
    ∀ {cs : List (Finset ℕ)}, cs.Pairwise Disjoint → (∀ X ∈ cs, X ⊆ Finset.range n) →
      (cs.map (Finset.image f)).Pairwise Disjoint
  | [], _, _ => List.Pairwise.nil
  | A :: _, hp, hsub => by
    rw [List.pairwise_cons] at hp
    rw [List.map_cons, List.pairwise_cons]
    refine ⟨?_, pairwise_disjoint_image hinj hp.2 fun Y hY => hsub Y (List.mem_cons_of_mem _ hY)⟩
    intro Y hY
    rcases List.mem_map.mp hY with ⟨B, hB, rfl⟩
    have hAsub := hsub A List.mem_cons_self
    have hBsub := hsub B (List.mem_cons_of_mem _ hB)
    have hdis := hp.1 B hB
    rw [Finset.disjoint_left]
    intro u huA huB
    rcases Finset.mem_image.mp huA with ⟨a, ha, rfl⟩
    rcases Finset.mem_image.mp huB with ⟨b, hb, hfab⟩
    have hab : a = b := hinj a b (Finset.mem_range.mp (hAsub ha)) (Finset.mem_range.mp (hBsub hb)) hfab.symm
    subst hab
    exact Finset.disjoint_left.mp hdis ha hb

lemma decomposeProp_of_compressed {G : Cited.Graph} {actVerts : List ℕ}
    (hact : ActVertsSpec G actVerts) {c_ℓ : ℝ} {d_ℓ : ℕ}
    {level : List ℕ} {rawComps : List (ℕ × List ℕ)} {φ : ℝ}
    (hprop : DecomposeProp c_ℓ (compressGraph actVerts G)
      (mkDecomposeOutput d_ℓ level rawComps) φ) :
    DecomposeProp c_ℓ G (mkDecomposeOutput d_ℓ level (liftRawComps actVerts rawComps)) φ := by
  set G_act := compressGraph actVerts G
  set d_act := mkDecomposeOutput d_ℓ level rawComps
  set d := mkDecomposeOutput d_ℓ level (liftRawComps actVerts rawComps)
  let f : ℕ → ℕ := fun i => actVerts.getD i 0
  let g : ℕ → ℕ := fun u => actVerts.idxOf u
  have hf_lt : ∀ i < actVerts.length, f i < G.n := fun i hi =>
    getD_lt_of_lt hi hact.lt_n
  have hf_inj : ∀ i j, i < actVerts.length → j < actVerts.length → f i = f j → i = j :=
    fun _ _ hi hj h => pairwise_lt_getD_inj hact.strict hi hj h
  have hgf : ∀ i < actVerts.length, g (f i) = i := fun i hi => hact.idxOf_getD hi
  have hfg : ∀ u ∈ actVerts, f (g u) = u := fun u hu => hact.getD_idxOf hu
  have hm_act_eq : G_act.m = G.m := compressGraph_m actVerts G
  have hcomps_eq : ∀ i, d.comps i = (d_act.comps i).map (Finset.image f) := by
    intro i
    simp only [d, d_act, mkDecomposeOutput, liftRawComps]
    have haux : ∀ cs : List (ℕ × List ℕ),
        ((cs.map fun c => (c.1, c.2.map f)).filter fun c => decide (c.1 = i)).map (fun c => c.2.toFinset) =
        ((cs.filter fun c => decide (c.1 = i)).map fun c => c.2.toFinset).map (Finset.image f) := by
      intro cs
      induction cs with
      | nil => simp
      | cons c cs ih =>
        simp only [List.map_cons, List.filter_cons]
        by_cases hc : c.1 = i <;> simp [hc, ih]
        ext u; simp [f]
    exact haux rawComps
  have hedges_eq : ∀ i, (d.graphAt G i).edges.map (fun e => (g e.1, g e.2)) =
      (d_act.graphAt G_act i).edges := by
    intro i
    simp only [DecomposeOutput.graphAt, DecomposeOutput.edgesAt, d, d_act, mkDecomposeOutput,
      hm_act_eq, List.map_map]
    refine List.map_congr_left fun j hj => ?_
    have hj' : j < G.m := List.mem_range.mp (List.mem_filter.mp hj).1
    change (g (G.edges.getD j (0, 0)).1, g (G.edges.getD j (0, 0)).2) =
      G_act.edges.getD j (0, 0)
    simp only [G_act, compressGraph, compressEdges, List.getD_eq_getElem?_getD,
      List.getElem?_map, List.getElem?_eq_getElem hj', Option.map_some, Option.getD_some]
    rfl
  have hedge_covers : ∀ i (e : ℕ × ℕ), e ∈ (d.graphAt G i).edges →
      e.1 ∈ actVerts ∧ e.2 ∈ actVerts := by
    intro i e he
    simp only [DecomposeOutput.graphAt, DecomposeOutput.edgesAt, List.mem_map,
      List.mem_filter, List.mem_range] at he
    rcases he with ⟨j, ⟨hj, _⟩, rfl⟩
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj, Option.getD_some]
    exact hact.covers _ (List.getElem_mem hj)
  have hmem_image : ∀ (S_act : Finset ℕ), S_act ⊆ G_act.verts →
      ∀ u ∈ actVerts, u ∈ S_act.image f ↔ g u ∈ S_act := by
    intro S_act hS u hu
    constructor
    · intro hmem
      rcases Finset.mem_image.mp hmem with ⟨k, hk, rfl⟩
      have hk_lt : k < actVerts.length := Finset.mem_range.mp (hS hk)
      rwa [hgf k hk_lt]
    · intro hgu
      exact Finset.mem_image.mpr ⟨g u, hgu, hfg u hu⟩
  rcases hprop with ⟨hℓ, hlev, hm_bound, hspec⟩
  refine ⟨by simpa [d, d_act, mkDecomposeOutput, hm_act_eq] using hℓ,
      fun j hj => hlev j (hm_act_eq ▸ hj),
      fun i hi => ?_, fun i hi0 hiℓ => ?_⟩
  · have hm_act := hm_bound i hi
    have hmeq : (d.graphAt G i).m = (d_act.graphAt G_act i).m := by
      simp [Cited.Graph.m, ← hedges_eq i]
    have hgn : G_act.n ≤ G.n := hact.length_le_n
    calc
      (d.graphAt G i).m = (d_act.graphAt G_act i).m := hmeq
      _ ≤ 2 ^ i * G_act.n := hm_act
      _ ≤ 2 ^ i * G.n := Nat.mul_le_mul_left _ hgn
  · rcases hspec i hi0 hiℓ with ⟨hdisj_act, hcomp_act, hcov_act⟩
    rw [hcomps_eq i]
    refine ⟨pairwise_disjoint_image hf_inj hdisj_act fun X hX => (hcomp_act X hX).1, ?_, ?_⟩
    · intro X hX
      rcases List.mem_map.mp hX with ⟨X_act, hX_act, rfl⟩
      rcases hcomp_act X_act hX_act with ⟨hXsub, hXcard, hXexp, hXdeg, hXcut⟩
      have hXverts : X_act.image f ⊆ G.verts := by
        intro u hu
        rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
        exact Finset.mem_range.mpr (hf_lt k (Finset.mem_range.mp (hXsub hk)))
      have hXcard' : 2 ≤ (X_act.image f).card := by
        rw [Finset.card_image_of_injOn fun a ha b hb h =>
          hf_inj a b (Finset.mem_range.mp (hXsub ha)) (Finset.mem_range.mp (hXsub hb)) h]
        exact hXcard
      have hinside : (d_act.graphAt G_act i).inside X_act =
          ((d.graphAt G i).inside (X_act.image f)).map (fun e => (g e.1, g e.2)) := by
        rw [Cited.Graph.inside, Cited.Graph.inside, ← hedges_eq i, List.filter_map]
        congr 1
        refine List.filter_congr fun e he => ?_
        have hcov := hedge_covers i e he
        have b1 : decide (g e.1 ∈ X_act) = decide (e.1 ∈ X_act.image f) :=
          decide_eq_decide.mpr (hmem_image X_act hXsub e.1 hcov.1).symm
        have b2 : decide (g e.2 ∈ X_act) = decide (e.2 ∈ X_act.image f) :=
          decide_eq_decide.mpr (hmem_image X_act hXsub e.2 hcov.2).symm
        dsimp only [Function.comp_def]
        rw [b1, b2]
      have hinside_cov : ∀ e ∈ (d.graphAt G i).inside (X_act.image f),
          e.1 ∈ actVerts ∧ e.2 ∈ actVerts := fun e he =>
        hedge_covers i e (List.mem_filter.mp he).1
      have hdeg_eq : ∀ k ∈ X_act, (d.graphAt G i).degIn (X_act.image f) (f k) =
          (d_act.graphAt G_act i).degIn X_act k := by
        intro k hk
        have hk_lt : k < actVerts.length := Finset.mem_range.mp (hXsub hk)
        simp only [Cited.Graph.degIn, hinside]
        have h1 := list_filter_map_length (fun e : ℕ × ℕ => (g e.1, g e.2))
          ((d.graphAt G i).inside (X_act.image f)) (fun e => decide (e.1 = k))
          (fun e => decide (e.1 = f k)) fun e he => by
            have he1 := (hinside_cov e he).1
            have : g e.1 = k ↔ e.1 = f k := ⟨fun h => by rw [← h, hfg _ he1], fun h => by rw [h, hgf k hk_lt]⟩
            exact decide_eq_decide.mpr this
        have h2 := list_filter_map_length (fun e : ℕ × ℕ => (g e.1, g e.2))
          ((d.graphAt G i).inside (X_act.image f)) (fun e => decide (e.2 = k))
          (fun e => decide (e.2 = f k)) fun e he => by
            have he2 := (hinside_cov e he).2
            have : g e.2 = k ↔ e.2 = f k := ⟨fun h => by rw [← h, hfg _ he2], fun h => by rw [h, hgf k hk_lt]⟩
            exact decide_eq_decide.mpr this
        omega
      refine ⟨hXverts, hXcard', ?_, ?_, ?_⟩
      · intro S hS hSne hSneX
        let S_act := S.image g
        have hSin_act : ∀ u ∈ S, u ∈ actVerts ∧ g u ∈ X_act := by
          intro u hu
          rcases Finset.mem_image.mp (hS hu) with ⟨k, hk, rfl⟩
          have hk_lt : k < actVerts.length := Finset.mem_range.mp (hXsub hk)
          exact ⟨by
            simp only [f, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk_lt, Option.getD_some]
            exact List.getElem_mem hk_lt,
            by rwa [hgf k hk_lt]⟩
        have hSact_sub : S_act ⊆ X_act := by
          intro k hk
          rcases Finset.mem_image.mp hk with ⟨u, hu, rfl⟩
          exact (hSin_act u hu).2
        have hS_eq : S = S_act.image f := by
          ext u
          constructor
          · intro hu
            exact Finset.mem_image.mpr ⟨g u, Finset.mem_image.mpr ⟨u, hu, rfl⟩,
              hfg u (hSin_act u hu).1⟩
          · intro hu
            rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
            rcases Finset.mem_image.mp hk with ⟨v, hv, hgv⟩
            have hgf_eq := congrArg f hgv
            rw [hfg v (hSin_act v hv).1] at hgf_eq
            rwa [← hgf_eq]
        have hdiff_eq : X_act.image f \ S = (X_act \ S_act).image f := by
          ext u
          rw [Finset.mem_sdiff, hS_eq]
          constructor
          · rintro ⟨huX, huS⟩
            rcases Finset.mem_image.mp huX with ⟨k, hk, rfl⟩
            refine Finset.mem_image.mpr ⟨k, Finset.mem_sdiff.mpr ⟨hk, fun hkS => ?_⟩, rfl⟩
            exact huS (Finset.mem_image.mpr ⟨k, hkS, rfl⟩)
          · rintro hu
            rcases Finset.mem_image.mp hu with ⟨k, hk, rfl⟩
            rcases Finset.mem_sdiff.mp hk with ⟨hkX, hkS⟩
            refine ⟨Finset.mem_image.mpr ⟨k, hkX, rfl⟩, fun huS => ?_⟩
            rcases Finset.mem_image.mp huS with ⟨a, ha, hfa⟩
            have heq_ak := hf_inj k a (Finset.mem_range.mp (hXsub hkX))
              (Finset.mem_range.mp (hXsub (hSact_sub ha))) hfa.symm
            rw [← heq_ak] at ha
            exact hkS ha
        have hSact_ne : S_act.Nonempty := hSne.image g
        have hSact_neX : S_act ≠ X_act := by
          intro heq
          apply hSneX
          rw [hS_eq, heq]
        have hvolS : (d.graphAt G i).volIn (X_act.image f) S =
            (d_act.graphAt G_act i).volIn X_act S_act := by
          rw [hS_eq, Cited.Graph.volIn, Cited.Graph.volIn, Finset.sum_image]
          · exact Finset.sum_congr rfl fun k hk => hdeg_eq k (hSact_sub hk)
          · intro a ha b hb hfab
            exact hf_inj a b (Finset.mem_range.mp (hXsub (hSact_sub ha)))
              (Finset.mem_range.mp (hXsub (hSact_sub hb))) hfab
        have hvolDiff : (d.graphAt G i).volIn (X_act.image f) (X_act.image f \ S) =
            (d_act.graphAt G_act i).volIn X_act (X_act \ S_act) := by
          rw [hdiff_eq, Cited.Graph.volIn, Cited.Graph.volIn, Finset.sum_image]
          · exact Finset.sum_congr rfl fun k hk => hdeg_eq k (Finset.mem_sdiff.mp hk).1
          · intro a ha b hb hfab
            exact hf_inj a b (Finset.mem_range.mp (hXsub (Finset.mem_sdiff.mp ha).1))
              (Finset.mem_range.mp (hXsub (Finset.mem_sdiff.mp hb).1)) hfab
        have hcut : (d.graphAt G i).cutIn (X_act.image f) S =
            (d_act.graphAt G_act i).cutIn X_act S_act := by
          rw [hS_eq, Cited.Graph.cutIn, Cited.Graph.cutIn, hinside]
          exact (list_filter_map_length (fun e : ℕ × ℕ => (g e.1, g e.2))
            ((d.graphAt G i).inside (X_act.image f))
            (fun e => decide (e.1 ∈ S_act) != decide (e.2 ∈ S_act))
            (fun e => decide (e.1 ∈ S_act.image f) != decide (e.2 ∈ S_act.image f))
            fun e he => by
              have hec := hinside_cov e he
              have b1 : decide (g e.1 ∈ S_act) = decide (e.1 ∈ S_act.image f) :=
                decide_eq_decide.mpr (hmem_image S_act (hSact_sub.trans hXsub) e.1 hec.1).symm
              have b2 : decide (g e.2 ∈ S_act) = decide (e.2 ∈ S_act.image f) :=
                decide_eq_decide.mpr (hmem_image S_act (hSact_sub.trans hXsub) e.2 hec.2).symm
              dsimp only
              rw [b1, b2])
        rw [hvolS, hvolDiff, hcut]
        exact hXexp S_act hSact_sub hSact_ne hSact_neX
      · intro x hx
        rcases Finset.mem_image.mp hx with ⟨k, hk, rfl⟩
        rw [hdeg_eq k hk]
        exact hXdeg k hk
      · intro e he
        have hcov := hedge_covers i e he
        have he' : (g e.1, g e.2) ∈ (d_act.graphAt G_act i).edges := by
          rw [← hedges_eq i]
          exact List.mem_map.mpr ⟨e, he, rfl⟩
        rw [hmem_image X_act hXsub e.1 hcov.1, hmem_image X_act hXsub e.2 hcov.2]
        exact hXcut (g e.1, g e.2) he'
    · intro e he
      have he' : (g e.1, g e.2) ∈ (d_act.graphAt G_act i).edges := by
        rw [← hedges_eq i]
        exact List.mem_map.mpr ⟨e, he, rfl⟩
      rcases hcov_act (g e.1, g e.2) he' with ⟨X_act, hX_act, h1, h2⟩
      have hXsub := (hcomp_act X_act hX_act).1
      have hcov := hedge_covers i e he
      refine ⟨X_act.image f, List.mem_map.mpr ⟨X_act, hX_act, rfl⟩,
        (hmem_image X_act hXsub e.1 hcov.1).mpr h1,
        (hmem_image X_act hXsub e.2 hcov.2).mpr h2⟩

/-! ## 2. Array Helpers, `listSwap`, `IsHeapRange`, and `SiftInv` -/

/-- Memory agrees with `mem` outside `[lo, hi)`. -/
def MemFrame (mem mem' : ℕ → ℕ) (lo hi : ℕ) : Prop :=
  ∀ a, a < lo ∨ hi ≤ a → mem' a = mem a

lemma memFrame_refl (mem : ℕ → ℕ) (lo hi : ℕ) : MemFrame mem mem lo hi :=
  fun _ _ => rfl

lemma memFrame_trans {m₁ m₂ m₃ : ℕ → ℕ} {lo hi : ℕ}
    (h12 : MemFrame m₁ m₂ lo hi) (h23 : MemFrame m₂ m₃ lo hi) :
    MemFrame m₁ m₃ lo hi :=
  fun a ha => (h23 a ha).trans (h12 a ha)

lemma memFrame_mono {m₁ m₂ : ℕ → ℕ} {lo lo' hi hi' : ℕ}
    (h : MemFrame m₁ m₂ lo' hi') (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    MemFrame m₁ m₂ lo hi :=
  fun a ha => h a (by omega)

lemma memFrame_update {mem : ℕ → ℕ} {a v lo hi : ℕ} (ha1 : lo ≤ a) (ha2 : a < hi) :
    MemFrame mem (Function.update mem a v) lo hi := by
  intro x hx
  apply Function.update_of_ne
  omega

lemma tab_update_set {mem : ℕ → ℕ} {base n j v : ℕ} (_hj : j < n) :
    tab n (fun i => Function.update mem (base + j) v (base + i)) =
      (tab n fun i => mem (base + i)).set j v := by
  apply List.ext_getElem
  · simp [tab]
  · intro i hi1 hi2
    simp only [tab, List.length_map, List.length_range] at hi1
    simp only [tab, List.getElem_map, List.getElem_range, List.getElem_set]
    split_ifs with hij
    · subst hij; simp
    · exact Function.update_of_ne (by omega) _ mem

/-- Swap elements `i` and `j` of a list `xs`. -/
def listSwap (xs : List ℕ) (i j : ℕ) : List ℕ :=
  (xs.set i (xs.getD j 0)).set j (xs.getD i 0)

lemma listSwap_length (xs : List ℕ) (i j : ℕ) : (listSwap xs i j).length = xs.length := by
  simp [listSwap]

lemma listSwap_perm (xs : List ℕ) {i j : ℕ} (hi : i < xs.length) (hj : j < xs.length) :
    (listSwap xs i j).Perm xs := by
  by_cases hij : i = j
  · subst hij
    have heq : listSwap xs i i = xs := by
      apply List.ext_getElem
      · simp [listSwap]
      · intro k hk1 hk2
        simp only [listSwap, List.getElem_set, List.getD_eq_getElem?_getD,
          List.getElem?_eq_getElem hi, Option.getD_some]
        split_ifs with hki
        · subst hki; rfl
        · rfl
    rw [heq]
  · rw [List.perm_iff_count]
    intro a
    simp only [listSwap]
    have hlen1 : j < (xs.set i (xs.getD j 0)).length := by simp [hj]
    rw [List.count_set hlen1, List.count_set hi, List.getElem_set_ne hij]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
      Option.getD_some]
    by_cases h1 : xs[i] = a <;> by_cases h2 : xs[j] = a
    · have h1pos : 1 ≤ List.count a xs := List.count_pos_iff.mpr (by rw [← h1]; exact List.getElem_mem hi)
      simp [h1, h2]; omega
    · have h1pos : 1 ≤ List.count a xs := List.count_pos_iff.mpr (by rw [← h1]; exact List.getElem_mem hi)
      simp [h1, h2]; omega
    · simp [h1, h2]
    · simp [h1, h2]

private lemma listSwap_getD {xs : List ℕ} {i j k : ℕ}
    (hi : i < xs.length) (hj : j < xs.length) (hk : k < xs.length) :
    (listSwap xs i j).getD k 0 =
      if k = j then xs.getD i 0 else if k = i then xs.getD j 0 else xs.getD k 0 := by
  simp only [listSwap, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem (by simp; exact hk : k < ((xs.set i _).set j _).length),
    List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem hk, Option.getD_some, List.getElem_set]
  split_ifs <;> first | rfl | omega

/-- Max-heap property on `xs[lo .. hi - 1]`. -/
def IsHeapRange (xs : List ℕ) (lo hi : ℕ) : Prop :=
  ∀ p, lo ≤ p →
    (∀ _ : 2 * p + 1 < hi, xs.getD (2 * p + 1) 0 ≤ xs.getD p 0) ∧
    (∀ _ : 2 * p + 2 < hi, xs.getD (2 * p + 2) 0 ≤ xs.getD p 0)

lemma isHeapRange_vacuous (xs : List ℕ) {lo hi : ℕ} (h : hi ≤ 2 * lo + 1) :
    IsHeapRange xs lo hi :=
  fun _ hp => ⟨fun h1 => by omega, fun h2 => by omega⟩

lemma isHeapRange_max (xs : List ℕ) {hi : ℕ} (hh : IsHeapRange xs 0 hi) :
    ∀ i < hi, xs.getD i 0 ≤ xs.getD 0 0 := by
  intro i
  induction i using Nat.strong_induction_on with
  | h i ih =>
    intro hi_lt
    rcases i with _ | i'
    · exact le_rfl
    · set p := i' / 2
      have hp_lt : p < i' + 1 := by omega
      have hpar := hh p (Nat.zero_le p)
      have hstep : xs.getD (i' + 1) 0 ≤ xs.getD p 0 := by
        rcases Nat.even_or_odd' i' with ⟨k, hk | hk⟩
        · have h1 : 2 * p + 1 = i' + 1 := by omega
          simpa [h1] using hpar.1 (by omega)
        · have h2 : 2 * p + 2 = i' + 1 := by omega
          simpa [h2] using hpar.2 (by omega)
      exact le_trans hstep (ih p hp_lt (by omega))

/-- Sift-down invariant for heapifying `[start, hi)`. -/
def SiftInv (xs : List ℕ) (start hi root flag : ℕ) : Prop :=
  start ≤ root ∧ root < hi ∧
  (∀ p, start ≤ p → p ≠ root →
    (2 * p + 1 < hi → xs.getD (2 * p + 1) 0 ≤ xs.getD p 0) ∧
    (2 * p + 2 < hi → xs.getD (2 * p + 2) 0 ≤ xs.getD p 0)) ∧
  (start < root →
    (2 * root + 1 < hi → xs.getD (2 * root + 1) 0 ≤ xs.getD ((root - 1) / 2) 0) ∧
    (2 * root + 2 < hi → xs.getD (2 * root + 2) 0 ≤ xs.getD ((root - 1) / 2) 0)) ∧
  (flag = 0 →
    (2 * root + 1 < hi → xs.getD (2 * root + 1) 0 ≤ xs.getD root 0) ∧
    (2 * root + 2 < hi → xs.getD (2 * root + 2) 0 ≤ xs.getD root 0))

lemma siftInv_init {xs : List ℕ} {start hi : ℕ} (hsh : start < hi)
    (hh : IsHeapRange xs (start + 1) hi) : SiftInv xs start hi start 1 :=
  ⟨le_rfl, hsh, fun p hp _ => hh p (by omega), fun h => by omega, fun h => by omega⟩

lemma siftInv_done {xs : List ℕ} {start hi root : ℕ} (h : SiftInv xs start hi root 0) :
    IsHeapRange xs start hi := by
  rcases h with ⟨_, _, hall, _, hzero⟩
  intro p hp
  by_cases hpr : p = root
  · subst hpr; exact hzero rfl
  · exact hall p hp hpr

lemma siftInv_swap {xs : List ℕ} {start hi root child : ℕ}
    (hi_le : hi ≤ xs.length)
    (hinv : SiftInv xs start hi root 1)
    (hch1 : child = 2 * root + 1 ∨ child = 2 * root + 2)
    (hch_lt : child < hi)
    (hsib : ∀ c2, c2 ∈ [2 * root + 1, 2 * root + 2] → c2 < hi → xs.getD c2 0 ≤ xs.getD child 0)
    (hlt : xs.getD root 0 < xs.getD child 0) :
    SiftInv (listSwap xs root child) start hi child 1 := by
  rcases hinv with ⟨hsr, hrh, hall, hpar, _⟩
  have hr_len : root < xs.length := lt_of_lt_of_le hrh hi_le
  have hc_len : child < xs.length := lt_of_lt_of_le hch_lt hi_le
  have hrc_ne : root ≠ child := by omega
  have hpar_eq : (child - 1) / 2 = root := by omega
  have h_get : ∀ k, k < hi → (listSwap xs root child).getD k 0 =
      if k = child then xs.getD root 0 else if k = root then xs.getD child 0 else xs.getD k 0 :=
    fun k hk => listSwap_getD hr_len hc_len (lt_of_lt_of_le hk hi_le)
  have hch_hall := hall child (by omega) (by omega)
  refine ⟨by omega, hch_lt, ?_, ?_, fun h => by omega⟩
  · intro p hp hpne
    by_cases hpr : p = root
    · refine ⟨fun h1 => ?_, fun h2 => ?_⟩
      · have h1' : 2 * root + 1 < hi := hpr ▸ h1
        rw [hpr, h_get (2 * root + 1) h1', h_get root hrh]
        split_ifs <;> first | exact le_of_lt hlt | exact hsib (2 * root + 1) (by simp) h1' | omega
      · have h2' : 2 * root + 2 < hi := hpr ▸ h2
        rw [hpr, h_get (2 * root + 2) h2', h_get root hrh]
        split_ifs <;> first | exact le_of_lt hlt | exact hsib (2 * root + 2) (by simp) h2' | omega
    · refine ⟨fun h1 => ?_, fun h2 => ?_⟩
      · by_cases h1r : 2 * p + 1 = root
        · have hsr_lt : start < root := by omega
          have hp_eq : p = (root - 1) / 2 := by omega
          rw [h_get (2 * p + 1) h1, h_get p (by omega)]
          split_ifs <;> try omega
          rw [hp_eq]
          rcases hch1 with rfl | rfl
          · exact (hpar hsr_lt).1 hch_lt
          · exact (hpar hsr_lt).2 hch_lt
        · rw [h_get (2 * p + 1) h1, h_get p (by omega)]
          split_ifs <;> first | exact (hall p hp hpr).1 h1 | omega
      · by_cases h2r : 2 * p + 2 = root
        · have hsr_lt : start < root := by omega
          have hp_eq : p = (root - 1) / 2 := by omega
          rw [h_get (2 * p + 2) h2, h_get p (by omega)]
          split_ifs <;> try omega
          rw [hp_eq]
          rcases hch1 with rfl | rfl
          · exact (hpar hsr_lt).1 hch_lt
          · exact (hpar hsr_lt).2 hch_lt
        · rw [h_get (2 * p + 2) h2, h_get p (by omega)]
          split_ifs <;> first | exact (hall p hp hpr).2 h2 | omega
  · intro _
    rw [hpar_eq]
    refine ⟨fun h1 => ?_, fun h2 => ?_⟩
    · rw [h_get (2 * child + 1) h1, h_get root hrh]
      split_ifs <;> first | exact hch_hall.1 h1 | omega
    · rw [h_get (2 * child + 2) h2, h_get root hrh]
      split_ifs <;> first | exact hch_hall.2 h2 | omega

end MinCostFlow.Expander
