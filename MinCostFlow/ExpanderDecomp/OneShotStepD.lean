module

public import MinCostFlow.ExpanderDecomp.OneShotHelpers
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.List.GetD
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Multi-call embedding composition and Step D of `OneShot`

This file proves the two final proof components of `OneShot` (Step D):
* `embed_calls`: composing the embeddings of at most `Δ` valid `RoutedCall`s together with their
  fake edges into a single embedding of `callsWitnessEdges calls` into `G + callsFakeEdges calls`
  on `X` with congestion at most `calls.length * R` on host edges and `1` on fake edges, fake
  degree at most `calls.length`, and total fake edge count at most `calls.length * z`.
* `stepD_removeFake`: given a spanning witness `callsWitnessEdges calls` of edge expansion at least
  `α / (40 * P (q - 1))` on `X` (`2 ≤ |X|`), applying the embedding lemma `isConductanceExpanderOn_of_embedding`
  and the fake-edge removal lemma `removeFake_spec` at `ρ = 12 / P_q` produces an induced expander `R ⊆ X` with
  `|R| ≥ 11 |X| / 12` and edge expansion at least `1 / P_q`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- Combined witness edges (routed + fake) across a list of routing calls. -/
def callsWitnessEdges (calls : List RoutedCall) : List (ℕ × ℕ) :=
  calls.flatMap fun c => c.routed ++ c.fake

/-- Combined fake edges across a list of routing calls. -/
def callsFakeEdges (calls : List RoutedCall) : List (ℕ × ℕ) :=
  calls.flatMap fun c => c.fake

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Composing embeddings across routing calls -/

private def shiftEdgeIdx (m off i : ℕ) : ℕ :=
  if i < m then i else i + off

private lemma isEdgeWalk_map_shift {E₁ E₂ : List (ℕ × ℕ)} (F : List (ℕ × ℕ)) {u v : ℕ}
    {es : List ℕ} (h : IsEdgeWalk (E₁ ++ E₂) u v es) :
    IsEdgeWalk (E₁ ++ F ++ E₂) u v (es.map (shiftEdgeIdx E₁.length F.length)) := by
  induction h with
  | nil u => exact IsEdgeWalk.nil u
  | @cons u x v j es hj hend _ ih =>
    rw [List.map_cons]
    have hlen : (E₁ ++ E₂).length = E₁.length + E₂.length := List.length_append
    have hlen' : (E₁ ++ F ++ E₂).length = E₁.length + F.length + E₂.length := by
      simp [List.length_append, Nat.add_assoc]
    have hlt : shiftEdgeIdx E₁.length F.length j < (E₁ ++ F ++ E₂).length := by
      unfold shiftEdgeIdx
      split_ifs <;> omega
    have hedge : edgeAt (E₁ ++ F ++ E₂) (shiftEdgeIdx E₁.length F.length j) =
        edgeAt (E₁ ++ E₂) j := by
      unfold edgeAt shiftEdgeIdx
      by_cases h1 : j < E₁.length
      · simp only [h1, ↓reduceIte]
        rw [List.append_assoc, List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h1]
      · simp only [h1, ↓reduceIte]
        have hlt2 : j + F.length < (E₁ ++ F ++ E₂).length := by omega
        rw [List.getD_eq_getElem _ _ hlt2, List.getD_eq_getElem _ _ hj]
        rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by omega)]
        have hidx : j + F.length - (E₁ ++ F).length = j - E₁.length := by
          simp [List.length_append]; omega
        simp only [hidx]
    exact IsEdgeWalk.cons hlt (hedge.symm ▸ hend) ih

private lemma congestion_append_witness (n : ℕ) (E₁ E₂ : List (ℕ × ℕ))
    (emb₁ emb₂ : ℕ → List ℕ) (i : ℕ) :
    congestion (Graph.mk n (E₁ ++ E₂))
      (fun j => if j < E₁.length then emb₁ j else emb₂ (j - E₁.length)) i =
      congestion (Graph.mk n E₁) emb₁ i + congestion (Graph.mk n E₂) emb₂ i := by
  unfold congestion Graph.m
  dsimp only
  rw [List.length_append]
  set S := (Finset.range (E₁.length + E₂.length)).filter
    fun j => i ∈ (if j < E₁.length then emb₁ j else emb₂ (j - E₁.length))
  set S₁ := (Finset.range E₁.length).filter fun j => i ∈ emb₁ j
  set S₂ := (Finset.range E₂.length).filter fun j => i ∈ emb₂ j
  have hsplit : S = S₁ ∪ S₂.image (fun j => E₁.length + j) := by
    ext j
    simp only [S, S₁, S₂, Finset.mem_union, Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨hj, hmem⟩
      by_cases h1 : j < E₁.length
      · simp only [h1, ↓reduceIte] at hmem
        exact Or.inl ⟨h1, hmem⟩
      · simp only [h1, ↓reduceIte] at hmem
        right
        exact ⟨j - E₁.length, ⟨by omega, hmem⟩, by omega⟩
    · rintro (⟨h1, hmem⟩ | ⟨k, ⟨hk, hmem⟩, rfl⟩)
      · exact ⟨by omega, by simp [h1, hmem]⟩
      · have hnot : ¬ (E₁.length + k < E₁.length) := by omega
        refine ⟨by omega, ?_⟩
        simp only [hnot, ↓reduceIte, Nat.add_sub_cancel_left]
        exact hmem
  have hdisj : Disjoint S₁ (S₂.image (fun j => E₁.length + j)) := by
    rw [Finset.disjoint_left]
    intro j hj1 hj2
    simp only [S₁, Finset.mem_filter, Finset.mem_range] at hj1
    simp only [Finset.mem_image] at hj2
    obtain ⟨k, _, rfl⟩ := hj2
    omega
  rw [hsplit, Finset.card_union_of_disjoint hdisj,
    Finset.card_image_of_injective _ (fun a b h => by omega)]

private lemma isEmbeddingOn_append_witness {n : ℕ} {E₁ E₂ : List (ℕ × ℕ)} {K : Graph}
    {X : Finset ℕ} {emb₁ emb₂ : ℕ → List ℕ}
    (h1 : IsEmbeddingOn (Graph.mk n E₁) K X emb₁)
    (h2 : IsEmbeddingOn (Graph.mk n E₂) K X emb₂) :
    IsEmbeddingOn (Graph.mk n (E₁ ++ E₂)) K X
      (fun j => if j < E₁.length then emb₁ j else emb₂ (j - E₁.length)) := by
  intro j hj hin
  have hj' : j < (E₁ ++ E₂).length := hj
  have hlen : (E₁ ++ E₂).length = E₁.length + E₂.length := List.length_append
  by_cases hlt : j < E₁.length
  · simp only [hlt, ↓reduceIte]
    have hedge : edgeAt (E₁ ++ E₂) j = edgeAt E₁ j := by
      unfold edgeAt
      exact List.getD_append _ _ _ _ hlt
    rw [hedge] at hin ⊢
    exact h1 j hlt hin
  · simp only [hlt, ↓reduceIte]
    have hlt2 : j - E₁.length < E₂.length := by omega
    have hedge : edgeAt (E₁ ++ E₂) j = edgeAt E₂ (j - E₁.length) := by
      unfold edgeAt
      rw [List.getD_eq_getElem _ _ hj', List.getD_eq_getElem _ _ hlt2,
        List.getElem_append_right (by omega)]
    rw [hedge] at hin ⊢
    exact h2 (j - E₁.length) hlt2 hin

/-- Embedding composition across a list of valid `RoutedCall`s:
* total fake edges `≤ calls.length * z`;
* fake degree in `X` at most `calls.length`;
* `callsWitnessEdges calls` embeds into `G + callsFakeEdges calls` on `X` with congestion at most
  `calls.length * R` on every edge of `G` and at most `1` on every fake edge. -/
theorem embed_calls {G : Graph} {X : Finset ℕ} {R z : ℕ}
    (calls : List RoutedCall) (hcalls : ∀ c ∈ calls, c.Valid G X R z) :
    (callsFakeEdges calls).length ≤ calls.length * z ∧
    (∀ e ∈ callsFakeEdges calls, e.1 ∈ X ∧ e.2 ∈ X) ∧
    (∀ v ∈ X, (Graph.mk G.n (callsFakeEdges calls)).degIn X v ≤ calls.length) ∧
    ∃ emb : ℕ → List ℕ,
      IsEmbeddingOn (Graph.mk G.n (callsWitnessEdges calls))
        (Graph.mk G.n (G.edges ++ callsFakeEdges calls)) X emb ∧
      (∀ i < G.m,
        congestion (Graph.mk G.n (callsWitnessEdges calls)) emb i ≤ calls.length * R) ∧
      (∀ i, G.m ≤ i →
        congestion (Graph.mk G.n (callsWitnessEdges calls)) emb i ≤ 1) := by
  induction calls with
  | nil =>
    refine ⟨by simp [callsFakeEdges], by simp [callsFakeEdges],
      by simp [callsFakeEdges, Graph.degIn, Graph.inside], fun _ => [], ?_, ?_, ?_⟩
    · intro j hj; simp [callsWitnessEdges, Graph.m] at hj
    · intro i _; simp [congestion]
    · intro i _; simp [congestion]
  | cons c rest ih =>
    have hc := hcalls c List.mem_cons_self
    have hrest_valid : ∀ c' ∈ rest, c'.Valid G X R z :=
      fun c' hc' => hcalls c' (List.mem_cons_of_mem _ hc')
    obtain ⟨hr_len, hr_mem, hr_deg, emb_r, hr_emb, hr_congG, hr_congF⟩ := ih hrest_valid
    obtain ⟨hc_rmem, hc_emb, hc_cong, hc_fmem, hc_fnd, hc_flen⟩ := hc
    have hfake_eq : callsFakeEdges (c :: rest) = c.fake ++ callsFakeEdges rest := by
      simp [callsFakeEdges]
    have hwit_eq : callsWitnessEdges (c :: rest) = (c.routed ++ c.fake) ++ callsWitnessEdges rest := by
      simp [callsWitnessEdges, List.append_assoc]
    have hlen_all : (callsFakeEdges (c :: rest)).length ≤ (c :: rest).length * z := by
      rw [hfake_eq, List.length_append, List.length_cons, Nat.succ_mul]
      omega
    have hmem_all : ∀ e ∈ callsFakeEdges (c :: rest), e.1 ∈ X ∧ e.2 ∈ X := by
      rw [hfake_eq]
      intro e he
      rcases List.mem_append.mp he with h | h
      · exact hc_fmem e h
      · exact hr_mem e h
    have hdeg_c : ∀ v ∈ X, (Graph.mk G.n c.fake).degIn X v ≤ 1 := by
      intro v _
      have h1 : ((Graph.mk G.n c.fake).inside X |>.filter fun e => e.1 = v).length ≤
          (c.fake.filter fun e => e.1 = v).length := by
        unfold Graph.inside
        rw [List.filter_filter]
        exact length_filter_le_of_imp c.fake fun e _ h => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢; exact h.1
      have h2 : ((Graph.mk G.n c.fake).inside X |>.filter fun e => e.2 = v).length ≤
          (c.fake.filter fun e => e.2 = v).length := by
        unfold Graph.inside
        rw [List.filter_filter]
        exact length_filter_le_of_imp c.fake fun e _ h => by
          simp only [Bool.and_eq_true, decide_eq_true_eq] at h ⊢; exact h.1
      have hsum_eq : (c.fake.filter fun e => e.1 = v).length +
          (c.fake.filter fun e => e.2 = v).length =
          (c.fake.flatMap fun e => [e.1, e.2]).count v := by
        clear h1 h2 hc_fnd hc_fmem hc_flen
        induction c.fake with
        | nil => simp
        | cons p t iht =>
          rcases p with ⟨a, b⟩
          simp only [List.filter_cons, List.flatMap_cons, List.cons_append, List.nil_append,
            List.count_cons, beq_iff_eq]
          by_cases ha : a = v <;> by_cases hb : b = v <;> simp [ha, hb] <;> omega
      have hcnt : (c.fake.flatMap fun e => [e.1, e.2]).count v ≤ 1 :=
        List.nodup_iff_count_le_one.mp hc_fnd v
      unfold Graph.degIn
      omega
    have hdeg_all : ∀ v ∈ X, (Graph.mk G.n (callsFakeEdges (c :: rest))).degIn X v ≤
        (c :: rest).length := by
      intro v hv
      rw [hfake_eq, degIn_append, List.length_cons]
      have h1 := hdeg_c v hv
      have h2 := hr_deg v hv
      omega
    set K := Graph.mk G.n (G.edges ++ (c.fake ++ callsFakeEdges rest))
    have hK_edges : K.edges = G.edges ++ c.fake ++ callsFakeEdges rest := by
      simp [K, List.append_assoc]
    -- (a) Embed `c.routed` into `K` via `c.emb`.
    have hemb_routed : IsEmbeddingOn (Graph.mk G.n c.routed) K X c.emb := by
      intro j hj hin
      obtain ⟨hw, hall⟩ := hc_emb j hj hin
      have hlift : ∀ {u v : ℕ} {es : List ℕ}, IsEdgeWalk G.edges u v es →
          IsEdgeWalk K.edges u v es := by
        intro u v es hwalk
        induction hwalk with
        | nil u => exact IsEdgeWalk.nil u
        | @cons u x v je es hje hend _ ihw =>
          have hlt' : je < K.edges.length := by
            simp only [K, List.length_append]; omega
          have hedge : edgeAt K.edges je = edgeAt G.edges je := by
            unfold edgeAt
            exact List.getD_append _ _ _ _ hje
          exact IsEdgeWalk.cons hlt' (hedge.symm ▸ hend) ihw
      refine ⟨hlift hw, fun i hi => ?_⟩
      have hiG : i < G.edges.length := hw.lt_length i hi
      have hedge : edgeAt K.edges i = edgeAt G.edges i := by
        unfold edgeAt; exact List.getD_append _ _ _ _ hiG
      rw [hedge]
      exact hall i hi
    have hcong_routed_F : ∀ i, G.m ≤ i → congestion (Graph.mk G.n c.routed) c.emb i = 0 := by
      intro i hi
      unfold congestion
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hj hmem
      have hjl : j < c.routed.length := Finset.mem_range.mp hj
      have heX : insideB X (edgeAt c.routed j) = true := by
        have he : edgeAt c.routed j ∈ c.routed := by
          unfold edgeAt; rw [List.getD_eq_getElem _ _ hjl]; exact List.getElem_mem hjl
        simp [insideB, (hc_rmem _ he).1, (hc_rmem _ he).2]
      have hlt := (hc_emb j hjl heX).1.lt_length i hmem
      unfold Graph.m at hi
      omega
    -- (b) Embed `c.fake` into `K` as single edges `[G.m + j]`.
    let emb_fake : ℕ → List ℕ := fun j => [G.m + j]
    have hemb_fake : IsEmbeddingOn (Graph.mk G.n c.fake) K X emb_fake := by
      intro j hj hin
      have hj' : j < c.fake.length := hj
      have hlt : G.m + j < K.edges.length := by
        simp only [K, Graph.m, List.length_append]; omega
      have hedge : edgeAt K.edges (G.m + j) = edgeAt c.fake j := by
        unfold edgeAt
        rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hj']
        simp only [K, Graph.m]
        rw [List.getElem_append_right (by omega)]
        simp only [Nat.add_sub_cancel_left]
        exact List.getElem_append_left hj'
      refine ⟨IsEdgeWalk.cons hlt (Or.inl ⟨by rw [hedge], by rw [hedge]⟩) (IsEdgeWalk.nil _), ?_⟩
      intro i hi
      simp only [emb_fake, List.mem_singleton] at hi
      rw [hi, hedge]
      exact hin
    have hcong_fake_G : ∀ i < G.m, congestion (Graph.mk G.n c.fake) emb_fake i = 0 := by
      intro i hi
      unfold congestion
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ hmem
      simp only [emb_fake, List.mem_singleton] at hmem
      omega
    have hcong_fake_F : ∀ i, congestion (Graph.mk G.n c.fake) emb_fake i ≤ 1 := by
      intro i
      unfold congestion
      have hsub : ((Finset.range (Graph.mk G.n c.fake).m).filter fun j => i ∈ emb_fake j) ⊆
          {i - G.m} := by
        intro j hj
        simp only [Finset.mem_filter, emb_fake, List.mem_singleton] at hj
        exact Finset.mem_singleton.mpr (by omega)
      exact le_trans (Finset.card_le_card hsub) (by simp)
    have hcong_fake_hi : ∀ i, G.m + c.fake.length ≤ i →
        congestion (Graph.mk G.n c.fake) emb_fake i = 0 := by
      intro i hi
      unfold congestion
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j hj hmem
      simp only [Finset.mem_range, Graph.m] at hj
      simp only [emb_fake, List.mem_singleton] at hmem
      omega
    -- (c) Shift `emb_r` from `G ++ callsFakeEdges rest` to `K = G ++ c.fake ++ callsFakeEdges rest`.
    let emb_r' : ℕ → List ℕ := fun j => (emb_r j).map (shiftEdgeIdx G.m c.fake.length)
    have hemb_rest : IsEmbeddingOn (Graph.mk G.n (callsWitnessEdges rest)) K X emb_r' := by
      intro j hj hin
      obtain ⟨hw, hall⟩ := hr_emb j hj hin
      refine ⟨?_, ?_⟩
      · rw [hK_edges]
        exact isEdgeWalk_map_shift c.fake hw
      · intro i hi
        obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hi
        have hklt : k < (G.edges ++ callsFakeEdges rest).length := hw.lt_length k hk
        have hedge : edgeAt K.edges (shiftEdgeIdx G.m c.fake.length k) =
            edgeAt (G.edges ++ callsFakeEdges rest) k := by
          rw [hK_edges]
          unfold edgeAt shiftEdgeIdx Graph.m
          by_cases h1 : k < G.edges.length
          · simp only [h1, ↓reduceIte]
            rw [List.append_assoc, List.getD_append _ _ _ _ h1, List.getD_append _ _ _ _ h1]
          · simp only [h1, ↓reduceIte]
            rw [List.length_append] at hklt
            rw [List.getD_eq_getElem _ _ (by simp [List.length_append]; omega),
              List.getD_eq_getElem _ _ (by rw [List.length_append]; omega)]
            rw [List.getElem_append_right (by simp; omega), List.getElem_append_right (by omega)]
            have hidx : k + c.fake.length - (G.edges ++ c.fake).length = k - G.edges.length := by
              simp [List.length_append]; omega
            simp only [hidx]
        rw [hedge]
        exact hall k hk
    have hcong_rest_G : ∀ i < G.m,
        congestion (Graph.mk G.n (callsWitnessEdges rest)) emb_r' i ≤ rest.length * R := by
      intro i hi
      have heq : congestion (Graph.mk G.n (callsWitnessEdges rest)) emb_r' i =
          congestion (Graph.mk G.n (callsWitnessEdges rest)) emb_r i := by
        unfold congestion
        congr 1
        apply Finset.filter_congr
        intro j _
        simp only [emb_r', List.mem_map]
        constructor
        · rintro ⟨k, hk, heq⟩
          have hki : k = i := by
            unfold shiftEdgeIdx at heq
            split_ifs at heq <;> omega
          exact hki ▸ hk
        · intro hi_mem
          exact ⟨i, hi_mem, by simp [shiftEdgeIdx, hi]⟩
      rw [heq]
      exact hr_congG i hi
    have hcong_rest_mid : ∀ i, G.m ≤ i → i < G.m + c.fake.length →
        congestion (Graph.mk G.n (callsWitnessEdges rest)) emb_r' i = 0 := by
      intro i hi1 hi2
      unfold congestion
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro j _ hmem
      obtain ⟨k, _, heq⟩ := List.mem_map.mp hmem
      unfold shiftEdgeIdx at heq
      split_ifs at heq <;> omega
    have hcong_rest_hi : ∀ i, G.m + c.fake.length ≤ i →
        congestion (Graph.mk G.n (callsWitnessEdges rest)) emb_r' i ≤ 1 := by
      intro i hi
      have heq : congestion (Graph.mk G.n (callsWitnessEdges rest)) emb_r' i =
          congestion (Graph.mk G.n (callsWitnessEdges rest)) emb_r (i - c.fake.length) := by
        unfold congestion
        congr 1
        apply Finset.filter_congr
        intro j _
        simp only [emb_r', List.mem_map]
        constructor
        · rintro ⟨k, hk, heq⟩
          have hki : k = i - c.fake.length := by
            unfold shiftEdgeIdx at heq
            split_ifs at heq <;> omega
          exact hki ▸ hk
        · intro hmem
          refine ⟨i - c.fake.length, hmem, ?_⟩
          unfold shiftEdgeIdx
          have hnot : ¬ (i - c.fake.length < G.m) := by omega
          simp only [hnot, ↓reduceIte]
          omega
      rw [heq]
      exact hr_congF (i - c.fake.length) (by omega)
    let emb_c := fun j => if j < c.routed.length then c.emb j else emb_fake (j - c.routed.length)
    let emb_all := fun j =>
      if j < (c.routed ++ c.fake).length then emb_c j
      else emb_r' (j - (c.routed ++ c.fake).length)
    have hemb_c : IsEmbeddingOn (Graph.mk G.n (c.routed ++ c.fake)) K X emb_c :=
      isEmbeddingOn_append_witness hemb_routed hemb_fake
    have hemb_all : IsEmbeddingOn (Graph.mk G.n (callsWitnessEdges (c :: rest)))
        (Graph.mk G.n (G.edges ++ callsFakeEdges (c :: rest))) X emb_all := by
      rw [hwit_eq, hfake_eq]
      exact isEmbeddingOn_append_witness hemb_c hemb_rest
    refine ⟨hlen_all, hmem_all, hdeg_all, emb_all, hemb_all, ?_, ?_⟩
    · intro i hi
      rw [hwit_eq, congestion_append_witness, congestion_append_witness]
      have h1 := hc_cong i hi
      have h2 := hcong_fake_G i hi
      have h3 := hcong_rest_G i hi
      rw [List.length_cons, Nat.succ_mul]
      omega
    · intro i hi
      rw [hwit_eq, congestion_append_witness, congestion_append_witness]
      have h1 := hcong_routed_F i hi
      by_cases hmid : i < G.m + c.fake.length
      · have h2 := hcong_fake_F i
        have h3 := hcong_rest_mid i hi hmid
        omega
      · have h2 := hcong_fake_hi i (by omega)
        have h3 := hcong_rest_hi i (by omega)
        omega

/-! ### Step D: removing fake edges -/

/-- **Step D of `OneShot`**: given `calls` with `calls.length ≤ cfg.Δ`, all valid against `G[X]`
with congestion `R_c` and deficit `z = |X| / D_q`, such that `callsWitnessEdges calls` has edge
expansion at least `α / (40 * P (q - 1))` on `X` (where `2 ≤ |X|`), calling `removeFake` at
`ρ = 12 / P_q` produces an induced subgraph `R ⊆ X` with `|R| ≥ 11 |X| / 12` and edge expansion
at least `1 / P_q`. -/
theorem stepD_removeFake {cfg : CoreParams} {r q : ℕ} (hcfg : CoreParamsValid cfg r)
    (hq1 : 1 ≤ q) (hqr : q ≤ r) {G : Graph} {X : Finset ℕ}
    (hX : X ⊆ Finset.range G.n) (hGvalid : G.IsValid) (hX2 : 2 ≤ X.card)
    (hdegG : ∀ v ∈ X, G.degIn X v ≤ cfg.Δ)
    {calls : List RoutedCall} (hcalls_len : calls.length ≤ cfg.Δ)
    (hcalls : ∀ c ∈ calls, c.Valid G X (routeCong cfg.Δ 100 cfg.L) (X.card / cfg.D q))
    (hwit_exp : (Graph.mk G.n (callsWitnessEdges calls)).IsExpansionExpanderOn X
      (cfg.α / (40 * (cfg.P (q - 1) : ℝ)))) :
    let F_all := callsFakeEdges calls
    let R := removeFake G.n G.edges F_all X (12 / (cfg.P q : ℝ))
    R ⊆ X ∧ 11 * X.card ≤ 12 * R.card ∧ G.IsExpansionExpanderOn R (1 / (cfg.P q : ℝ)) := by
  dsimp only
  set F_all := callsFakeEdges calls
  set R_c := routeCong cfg.Δ 100 cfg.L
  set K := Graph.mk G.n (G.edges ++ F_all)
  set W := Graph.mk G.n (callsWitnessEdges calls)
  have hRc_pos : 1 ≤ R_c := hcfg.routeCong_pos
  have hΔ_pos : 1 ≤ cfg.Δ := hcfg.hΔ_pos
  obtain ⟨hFlen, hFmem, hFdeg, emb, hemb, hcongG, hcongF⟩ := embed_calls calls hcalls
  set η := cfg.Δ * R_c
  have hη_pos : 0 < η := Nat.mul_pos hΔ_pos hRc_pos
  have hcong_all : ∀ i < K.m, congestion W emb i ≤ η := by
    intro i _
    by_cases hi : i < G.m
    · exact le_trans (hcongG i hi) (Nat.mul_le_mul_right R_c hcalls_len)
    · exact le_trans (hcongF i (by omega)) hη_pos
  have hdegK : ∀ v ∈ X, K.degIn X v ≤ 2 * cfg.Δ := by
    intro v hv
    show (Graph.mk G.n (G.edges ++ F_all)).degIn X v ≤ 2 * cfg.Δ
    rw [degIn_append]
    have h1 : (Graph.mk G.n G.edges).degIn X v ≤ cfg.Δ := hdegG v hv
    have h2 : (Graph.mk G.n F_all).degIn X v ≤ calls.length := hFdeg v hv
    omega
  have hPprev_pos : (0 : ℝ) < cfg.P (q - 1) :=
    Nat.cast_pos.mpr (hcfg.hP_pos (by omega))
  have hPq_pos : (0 : ℝ) < cfg.P q :=
    Nat.cast_pos.mpr (hcfg.hP_pos hqr)
  have hψW_pos : 0 < cfg.α / (40 * (cfg.P (q - 1) : ℝ)) :=
    div_pos hcfg.hα0 (by positivity)
  have hK_cond0 : K.IsConductanceExpanderOn X
      ((cfg.α / (40 * (cfg.P (q - 1) : ℝ))) / ((η : ℝ) * ((2 * cfg.Δ : ℕ) : ℝ))) :=
    isConductanceExpanderOn_of_embedding hemb hcong_all hη_pos hψW_pos.le hwit_exp
      (by omega : 0 < 2 * cfg.Δ) hdegK
  set ρ : ℝ := 12 / (cfg.P q : ℝ)
  have hρ0 : 0 < ρ := div_pos (by norm_num) hPq_pos
  have hρ1 : ρ ≤ 1 := by
    rw [div_le_one hPq_pos]
    exact_mod_cast hcfg.hP12 q hq1 hqr
  have hρ_le : ρ ≤ (cfg.α / (40 * (cfg.P (q - 1) : ℝ))) / ((η : ℝ) * ((2 * cfg.Δ : ℕ) : ℝ)) := by
    have hstep := hcfg.hPstep q hq1 hqr
    have hΔr : (0 : ℝ) < cfg.Δ := Nat.cast_pos.mpr hΔ_pos
    have hRcr : (0 : ℝ) < R_c := Nat.cast_pos.mpr hRc_pos
    have hden_pos : (0 : ℝ) < (η : ℝ) * ((2 * cfg.Δ : ℕ) : ℝ) := by
      push_cast [η]; positivity
    rw [div_le_div_iff₀ hPq_pos hden_pos]
    rw [div_mul_eq_mul_div, le_div_iff₀ (by positivity : (0 : ℝ) < 40 * (cfg.P (q - 1) : ℝ))]
    have hcast : (η : ℝ) * ((2 * cfg.Δ : ℕ) : ℝ) = 2 * (cfg.Δ : ℝ) ^ 2 * (R_c : ℝ) := by
      push_cast [η]; ring
    rw [hcast]
    nlinarith
  have hK_cond : K.IsConductanceExpanderOn X ρ :=
    isConductanceExpanderOn_mono hρ_le hK_cond0
  have hdegK_pos : ∀ v ∈ X, 1 ≤ K.degIn X v := by
    intro v hv
    have hsub : ({v} : Finset ℕ) ⊆ X := Finset.singleton_subset_iff.mpr hv
    have hne : ({v} : Finset ℕ).Nonempty := Finset.singleton_nonempty v
    have hneX : ({v} : Finset ℕ) ≠ X := by
      intro heq
      have hcard := congrArg Finset.card heq
      simp only [Finset.card_singleton] at hcard
      omega
    have hcutW := hwit_exp {v} hsub hne hneX
    have hsd_pos : 1 ≤ (X \ {v}).card := by
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_singleton]
      omega
    have hmin1 : (1 : ℝ) ≤ min (({v} : Finset ℕ).card : ℝ) ((X \ {v}).card : ℝ) := by
      simp only [Finset.card_singleton, Nat.cast_one]
      exact le_min (le_refl 1) (by exact_mod_cast hsd_pos)
    have hWpos : (0 : ℝ) < (W.cutIn X {v} : ℝ) :=
      lt_of_lt_of_le (by nlinarith) hcutW
    have hW1 : 1 ≤ W.cutIn X {v} := by
      have : (0 : ℕ) < W.cutIn X {v} := by exact_mod_cast hWpos
      omega
    have hcutK_mul : W.cutIn X {v} ≤ K.cutIn X {v} * η :=
      cutIn_le_mul_of_embedding hemb hcong_all {v}
    have hK1 : 1 ≤ K.cutIn X {v} := by
      by_contra h0
      have hk0 : K.cutIn X {v} = 0 := by omega
      rw [hk0, zero_mul] at hcutK_mul
      omega
    have hvol := cutIn_le_volIn K X {v}
    simp only [Graph.volIn, Finset.sum_singleton] at hvol
    omega
  have hG_edges : ∀ e ∈ G.edges, e.1 < G.n ∧ e.2 < G.n := hGvalid
  obtain ⟨hRsub, hRcond, hRdeg, hRvol⟩ :=
    removeFake_spec hX hG_edges hFmem hρ0 hρ1 hK_cond hdegK_pos
  set R := removeFake G.n G.edges F_all X ρ
  have hcard_le_vol : ((X \ R).card : ℝ) ≤ (K.volIn X (X \ R) : ℝ) := by
    exact_mod_cast card_le_volIn fun v hv => hdegK_pos v (Finset.sdiff_subset hv)
  have hFlen_r : (F_all.length : ℝ) ≤ (cfg.Δ : ℝ) * ((X.card / cfg.D q : ℕ) : ℝ) := by
    have hnat : F_all.length ≤ cfg.Δ * (X.card / cfg.D q) :=
      le_trans hFlen (Nat.mul_le_mul_right _ hcalls_len)
    exact_mod_cast hnat
  have hDq_pos : (0 : ℝ) < cfg.D q := Nat.cast_pos.mpr (hcfg.hD_pos hq1 hqr)
  have hz_le : ((X.card / cfg.D q : ℕ) : ℝ) ≤ (X.card : ℝ) / (cfg.D q : ℝ) := by
    rw [le_div_iff₀ hDq_pos]
    exact_mod_cast Nat.div_mul_le_self X.card (cfg.D q)
  have hDq_ge : (60 : ℝ) * (cfg.Δ : ℝ) * (cfg.P q : ℝ) ≤ (cfg.D q : ℝ) := by
    exact_mod_cast hcfg.hD q hq1 hqr
  have hrem_le : ((X \ R).card : ℝ) ≤ (X.card : ℝ) / 12 := by
    have h60 : 60 / ρ = 5 * (cfg.P q : ℝ) := by
      dsimp only [ρ]; field_simp; ring
    have h1 : ((X \ R).card : ℝ) ≤ 5 * (cfg.P q : ℝ) * (F_all.length : ℝ) := by
      rw [h60] at hRvol
      exact le_trans hcard_le_vol hRvol
    have h2 : 5 * (cfg.P q : ℝ) * (F_all.length : ℝ) ≤
        5 * (cfg.P q : ℝ) * ((cfg.Δ : ℝ) * ((X.card : ℝ) / (cfg.D q : ℝ))) := by
      have h3 : (F_all.length : ℝ) ≤ (cfg.Δ : ℝ) * ((X.card : ℝ) / (cfg.D q : ℝ)) :=
        le_trans hFlen_r (mul_le_mul_of_nonneg_left hz_le (Nat.cast_nonneg _))
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have h3 : 5 * (cfg.P q : ℝ) * ((cfg.Δ : ℝ) * ((X.card : ℝ) / (cfg.D q : ℝ))) ≤
        (X.card : ℝ) / 12 := by
      rw [show 5 * (cfg.P q : ℝ) * ((cfg.Δ : ℝ) * ((X.card : ℝ) / (cfg.D q : ℝ))) =
        (5 * (cfg.P q : ℝ) * (cfg.Δ : ℝ) * (X.card : ℝ)) / (cfg.D q : ℝ) by ring]
      rw [div_le_div_iff₀ hDq_pos (by norm_num : (0 : ℝ) < 12)]
      nlinarith
    exact le_trans h1 (le_trans h2 h3)
  have hrem_nat : 12 * (X \ R).card ≤ X.card := by
    have : (12 : ℝ) * ((X \ R).card : ℝ) ≤ (X.card : ℝ) := by linarith
    exact_mod_cast this
  have hRcard : 11 * X.card ≤ 12 * R.card := by
    have hadd : (X \ R).card + R.card = X.card := Finset.card_sdiff_add_card_eq_card hRsub
    omega
  have hφ_le : 1 / (cfg.P q : ℝ) ≤ ρ / 9 := by
    dsimp only [ρ]
    rw [div_div, div_le_div_iff₀ hPq_pos (by positivity)]
    linarith
  have hRcond' : (Graph.mk G.n G.edges).IsConductanceExpanderOn R (1 / (cfg.P q : ℝ)) :=
    isConductanceExpanderOn_mono hφ_le hRcond
  have hRexp : G.IsExpansionExpanderOn R (1 / (cfg.P q : ℝ)) := by
    cases G with
    | mk gn ge =>
      exact isExpansionExpanderOn_of_conductance_minDeg (by positivity) hRcond' hRdeg
  exact ⟨hRsub, hRcard, hRexp⟩

end MinCostFlow.ExpanderDecomp
