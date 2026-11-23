module

public import MinCostFlow.SparseCore.SparseCoreParams
public import MinCostFlow.SparseCore.BundleConstants
public import MinCostFlow.SparseCore.GraphHelpers
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Spanner Charge Bounds, Graph Normalization, and Parameter Envelopes

Shared foundations for charging bucket-spanner initializations and updates in the sparse-core
machine-cost model by the same formulas that the Word RAM dynamic-spanner contract pays, and for
normalizing bundle graphs off their edge sets so the model's `DynSpannerState` matches the
machine's `DSHist` literally.

* `normGraph G` zeroes `tail` and `head` outside `G.E`, matching `graphOfLists` and
  `Restart.normGraph` definitionally. `normGraph_graphEq` relates `normGraph G` and `G` via
  `GraphEq`, and `graphEq_*` transfers walks, subgraphs, embeddings, congestion, and active
  vertices across `GraphEq`.
* `SparsifyParamsLe` and `monoSparsifyParamsEnvelope` compare `SparsifyParams` pointwise and
  build a monotone envelope over `m ≤ M` preserving `SparsifySpec` and subpolynomial bounds.
* `spanInitBound` bounds a bucket-spanner initialization (`phaseBase`, `dsInitCoreCost`, and
  initial bank `dsInitBank`) in terms of `SparsifyParams`, `L`, `splitBound`, and `Hb`.
* `spanBatchRate` and `spanBatchCharge` match `dsBatchRate` and `dsBatchCharge` (without the
  implementation-dependent constant `dsAmortConst`), giving direct comparisons against `batchEnc`
  and the Theorem 8.2 amortized rate.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow
open MinCostFlow.LSF
open MinCostFlow.DynSpanner

/-! ## 1. Normalized graphs and `GraphEq` helpers -/

/-- The graph `G` with `tail` and `head` set to `0` at every name that is not an edge. -/
def normGraph (G : MGraph) : MGraph where
  V := G.V
  E := G.E
  tail e := if e ∈ G.E then G.tail e else 0
  head e := if e ∈ G.E then G.head e else 0

@[simp] lemma normGraph_V (G : MGraph) : (normGraph G).V = G.V := rfl
@[simp] lemma normGraph_E (G : MGraph) : (normGraph G).E = G.E := rfl
@[simp] lemma normGraph_n (G : MGraph) : (normGraph G).n = G.n := rfl
@[simp] lemma normGraph_m (G : MGraph) : (normGraph G).m = G.m := rfl

lemma normGraph_tail_of_mem {G : MGraph} {e : ℕ} (he : e ∈ G.E) :
    (normGraph G).tail e = G.tail e := by
  simp [normGraph, he]

lemma normGraph_head_of_mem {G : MGraph} {e : ℕ} (he : e ∈ G.E) :
    (normGraph G).head e = G.head e := by
  simp [normGraph, he]

lemma normGraph_graphEq (G : MGraph) : GraphEq (normGraph G) G :=
  ⟨rfl, rfl, fun _ he => ⟨normGraph_tail_of_mem he, normGraph_head_of_mem he⟩⟩

lemma normGraph_isValid {G : MGraph} (hV : G.IsValid) : (normGraph G).IsValid :=
  graphEq_isValid (graphEq_symm (normGraph_graphEq G)) hV

lemma normGraph_deg (G : MGraph) (v : ℕ) : (normGraph G).deg v = G.deg v :=
  graphEq_deg (normGraph_graphEq G) v

lemma normGraph_maxDeg (G : MGraph) : (normGraph G).maxDeg = G.maxDeg :=
  graphEq_maxDeg (normGraph_graphEq G)

lemma normGraph_eq_of_graphEq {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) :
    normGraph G₁ = normGraph G₂ := by
  rcases h with ⟨hV, hE, hEnds⟩
  cases G₁ with | mk V₁ E₁ t₁ h₁ =>
  cases G₂ with | mk V₂ E₂ t₂ h₂ =>
  dsimp only at hV hE hEnds
  subst hV; subst hE
  simp only [normGraph, MGraph.mk.injEq, true_and]
  constructor
  · funext e
    by_cases he : e ∈ E₁
    · simp only [he, ↓reduceIte]; exact (hEnds e he).1
    · simp [he]
  · funext e
    by_cases he : e ∈ E₁
    · simp only [he, ↓reduceIte]; exact (hEnds e he).2
    · simp [he]

lemma graphEq_src_of_mem {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) {x : ℕ × Bool} (hx : x.1 ∈ G₁.E) :
    G₁.src x = G₂.src x := by
  rcases x with ⟨e, b⟩
  cases b <;> simp [MGraph.src, (h.2.2 e hx).1, (h.2.2 e hx).2]

lemma graphEq_dst_of_mem {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) {x : ℕ × Bool} (hx : x.1 ∈ G₁.E) :
    G₁.dst x = G₂.dst x := by
  rcases x with ⟨e, b⟩
  cases b <;> simp [MGraph.dst, (h.2.2 e hx).1, (h.2.2 e hx).2]

lemma graphEq_activeSubgraph_n {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) :
    (activeSubgraph G₁).n = (activeSubgraph G₂).n := by
  unfold MGraph.n activeSubgraph
  have hdeg : G₁.deg = G₂.deg := funext (graphEq_deg h)
  rw [h.1, hdeg]

lemma normGraph_activeSubgraph_n (G : MGraph) :
    (activeSubgraph (normGraph G)).n = (activeSubgraph G).n :=
  graphEq_activeSubgraph_n (normGraph_graphEq G)

lemma graphEq_isWalk {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : G₁.IsWalk u v P) : G₂.IsWalk u v P := by
  induction hW with
  | nil => exact .nil _
  | cons he hsrc _ ih =>
    have he₂ : _ ∈ G₂.E := h.2.1 ▸ he
    have hsrc₂ : G₂.src _ = _ := (graphEq_src_of_mem h he).symm.trans hsrc
    have hdst := graphEq_dst_of_mem h he
    rw [hdst] at ih
    exact .cons he₂ hsrc₂ ih

lemma graphEq_walkVertices {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) {u v : ℕ} {P : List (ℕ × Bool)}
    (hW : G₁.IsWalk u v P) : G₁.walkVertices u P = G₂.walkVertices u P := by
  unfold MGraph.walkVertices
  congr 1
  refine List.map_congr_left fun x hx => ?_
  exact graphEq_dst_of_mem h (DynSpanner.IsWalk.mem_edge hW x hx)

lemma graphEq_isSubgraph_left {G₁ G₂ H : MGraph} (h : GraphEq G₁ G₂) (hsub : G₁.IsSubgraph H) :
    G₂.IsSubgraph H := by
  rcases hsub with ⟨hV, hE, hEnds⟩
  refine ⟨h.1 ▸ hV, h.2.1 ▸ hE, fun e he => ?_⟩
  have he₁ : e ∈ G₁.E := hE he
  exact ⟨(hEnds e he).1.trans (h.2.2 e he₁).1, (hEnds e he).2.trans (h.2.2 e he₁).2⟩

lemma graphEq_isSubgraph_right {G H₁ H₂ : MGraph} (h : GraphEq H₁ H₂) (hsub : G.IsSubgraph H₁) :
    G.IsSubgraph H₂ := by
  rcases hsub with ⟨hV, hE, hEnds⟩
  refine ⟨h.1 ▸ hV, h.2.1 ▸ hE, fun e he => ?_⟩
  have he₁ : e ∈ H₁.E := h.2.1.symm ▸ he
  exact ⟨(h.2.2 e he₁).1.symm.trans (hEnds e he₁).1, (h.2.2 e he₁).2.symm.trans (hEnds e he₁).2⟩

lemma graphEq_isEmbedding_left {G₁ G₂ H : MGraph} (h : GraphEq G₁ G₂) {emb : Embedding}
    (hEmb : emb.IsEmbedding G₁ H) : emb.IsEmbedding G₂ H := by
  refine ⟨h.1 ▸ hEmb.1, fun e he => ?_⟩
  have he₁ : e ∈ G₁.E := h.2.1.symm ▸ he
  have hW := hEmb.2 e he₁
  rwa [(h.2.2 e he₁).1, (h.2.2 e he₁).2] at hW

lemma graphEq_isEmbedding_right {G H₁ H₂ : MGraph} (h : GraphEq H₁ H₂) {emb : Embedding}
    (hEmb : emb.IsEmbedding G H₁) : emb.IsEmbedding G H₂ :=
  ⟨h.1 ▸ hEmb.1, fun e he => graphEq_isWalk h (hEmb.2 e he)⟩

lemma graphEq_emb_length {G₁ G₂ : MGraph} (h : GraphEq G₁ G₂) (emb : Embedding) :
    emb.length G₁ = emb.length G₂ := by
  unfold Embedding.length
  rw [h.2.1]

lemma graphEq_emb_vcongAt {G₁ G₂ H : MGraph} (h : GraphEq G₁ G₂) (emb : Embedding)
    (w : ℕ → ℝ) (v : ℕ) :
    emb.vcongAt G₁ H w v = emb.vcongAt G₂ H w v := by
  unfold Embedding.vcongAt
  have hfilt : (G₁.E.filter fun e => v ∈ H.walkVertices (G₁.tail e) (emb e)) =
      (G₂.E.filter fun e => v ∈ H.walkVertices (G₂.tail e) (emb e)) := by
    ext e
    simp only [Finset.mem_filter]
    constructor <;> rintro ⟨he, hv⟩
    · exact ⟨h.2.1 ▸ he, (h.2.2 e he).1 ▸ hv⟩
    · have he₁ : e ∈ G₁.E := h.2.1.symm ▸ he
      exact ⟨he₁, (h.2.2 e he₁).1.symm ▸ hv⟩
  rw [hfilt]

lemma graphEq_emb_vcong {G₁ G₂ H : MGraph} (h : GraphEq G₁ G₂) (emb : Embedding) (w : ℕ → ℝ) :
    emb.vcong G₁ H w = emb.vcong G₂ H w := by
  unfold Embedding.vcong
  have h1 : emb.vcongAt G₁ H w = emb.vcongAt G₂ H w := funext (graphEq_emb_vcongAt h emb w)
  rw [h1]

/-! ## 2. Pointwise ordering and monotone envelope on `SparsifyParams` -/

/-- Pointwise inequality on the six fields of `SparsifyParams` read by `SparsifySpec` and the
sparse-core cost bounds. -/
def SparsifyParamsLe (P₁ P₂ : SparsifyParams) : Prop :=
  P₁.γ_c ≤ P₂.γ_c ∧ P₁.γ_ℓ ≤ P₂.γ_ℓ ∧ P₁.K_s ≤ P₂.K_s ∧ P₁.p_s ≤ P₂.p_s ∧
    P₁.K_t ≤ P₂.K_t ∧ P₁.p_t ≤ P₂.p_t

lemma sparsifyParamsLe_refl (P : SparsifyParams) : SparsifyParamsLe P P :=
  ⟨le_rfl, le_rfl, le_rfl, le_rfl, le_rfl, le_rfl⟩

lemma sparsifyParamsLe_trans {P₁ P₂ P₃ : SparsifyParams}
    (h₁₂ : SparsifyParamsLe P₁ P₂) (h₂₃ : SparsifyParamsLe P₂ P₃) :
    SparsifyParamsLe P₁ P₃ :=
  ⟨le_trans h₁₂.1 h₂₃.1, le_trans h₁₂.2.1 h₂₃.2.1, le_trans h₁₂.2.2.1 h₂₃.2.2.1,
    le_trans h₁₂.2.2.2.1 h₂₃.2.2.2.1, le_trans h₁₂.2.2.2.2.1 h₂₃.2.2.2.2.1,
    le_trans h₁₂.2.2.2.2.2 h₂₃.2.2.2.2.2⟩

private lemma one_le_one_add_log_of_one_le {x : ℝ} (hx : 1 ≤ x) : 1 ≤ 1 + Real.log x := by
  linarith [Real.log_nonneg hx]

lemma sparsifySpec_of_le {mMax : ℕ} {P₁ P₂ : SparsifyParams}
    {sparsify : MGraph → MGraph → Embedding → SparsifyOut}
    (hLe : SparsifyParamsLe P₁ P₂) (hSp : SparsifySpec mMax P₁ sparsify) :
    SparsifySpec mMax P₂ sparsify := by
  intro H' J embJH hH' hJ hJm hlen hEmb
  obtain ⟨hSub, hOutEmb, hVcong, hLen, hM, hCost⟩ := hSp H' J embJH hH' hJ hJm hlen hEmb
  have hlog : (1 : ℝ) ≤ 1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2) :=
    one_le_one_add_log_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) J.n, Nat.cast_nonneg (α := ℝ) J.m])
  have hv_nn : 0 ≤ embJH.vcong J H' (fun _ => 1) := by
    unfold Embedding.vcong
    split_ifs with hV
    · obtain ⟨v, hv⟩ := hV
      refine le_trans ?_ (Finset.le_sup' (f := embJH.vcongAt J H' (fun _ => 1)) hv)
      unfold Embedding.vcongAt
      exact Finset.sum_nonneg fun _ _ => zero_le_one
    · exact le_rfl
  have hγ1 : 0 ≤ P₁.γ_ℓ := by linarith [P₁.hγ_ℓ]
  have hγ2 : 0 ≤ P₂.γ_ℓ := by linarith [P₂.hγ_ℓ]
  have hKs1 : 0 ≤ P₁.K_s := P₁.hK_s
  have hKs2 : 0 ≤ P₂.K_s := P₂.hK_s
  have hKt1 : 0 ≤ P₁.K_t := P₁.hK_t
  have hKt2 : 0 ≤ P₂.K_t := P₂.hK_t
  refine ⟨hSub, hOutEmb, ?_, ?_, ?_, ?_⟩
  · exact le_trans hVcong (by
      have := hLe.1
      have hlen_nn : (0 : ℝ) ≤ (embJH.length J : ℝ) := Nat.cast_nonneg _
      have hdeg_nn : (0 : ℝ) ≤ (J.maxDeg : ℝ) := Nat.cast_nonneg _
      gcongr)
  · exact le_trans hLen (mul_le_mul_of_nonneg_right hLe.2.1 (Nat.cast_nonneg _))
  · have hps := pow_le_pow_right₀ hlog hLe.2.2.2.1
    calc ((sparsify H' J embJH).Jtilde.m : ℝ)
        ≤ P₁.K_s * (J.n : ℝ) * P₁.γ_ℓ *
            (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P₁.p_s := hM
      _ ≤ P₂.K_s * (J.n : ℝ) * P₂.γ_ℓ *
            (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P₂.p_s := by
          have := hLe.2.1; have := hLe.2.2.1; gcongr
  · have hpt := pow_le_pow_right₀ hlog hLe.2.2.2.2.2
    calc ((sparsify H' J embJH).cost : ℝ)
        ≤ P₁.K_t * ((J.n : ℝ) + (J.m : ℝ) * P₁.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
            (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P₁.p_t := hCost
      _ ≤ P₂.K_t * ((J.n : ℝ) + (J.m : ℝ) * P₂.γ_ℓ ^ 2 * (embJH.length J : ℝ)) *
            (1 + Real.log ((J.n : ℝ) + (J.m : ℝ) + 2)) ^ P₂.p_t := by
          have := hLe.2.1; have := hLe.2.2.2.2.1; gcongr

/-- Minimal default `SparsifyParams`, used by pure-model initializers that do not read `machCost`. -/
def defaultSparsifyParams : SparsifyParams where
  γ_c := 1
  γ_ℓ := 1
  K_s := 0
  p_s := 0
  K_t := 0
  p_t := 0
  hγ_c := le_rfl
  hγ_ℓ := le_rfl
  hK_s := le_rfl
  hK_t := le_rfl

/-- Pointwise monotone upper envelope of a `SparsifyParams` family: at `m`, each of the six fields
takes its supremum over `0, …, m`. -/
noncomputable def monoSparsifyParamsEnvelope (params : ℕ → SparsifyParams) (m : ℕ) :
    SparsifyParams where
  γ_c := (Finset.range (m + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m)⟩
    (fun i => (params i).γ_c)
  γ_ℓ := (Finset.range (m + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m)⟩
    (fun i => (params i).γ_ℓ)
  K_s := (Finset.range (m + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m)⟩
    (fun i => (params i).K_s)
  p_s := (Finset.range (m + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m)⟩
    (fun i => (params i).p_s)
  K_t := (Finset.range (m + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m)⟩
    (fun i => (params i).K_t)
  p_t := (Finset.range (m + 1)).sup' ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m)⟩
    (fun i => (params i).p_t)
  hγ_c := le_trans (params 0).hγ_c
    (Finset.le_sup' (fun i => (params i).γ_c) (Finset.mem_range.mpr (Nat.zero_lt_succ m)))
  hγ_ℓ := le_trans (params 0).hγ_ℓ
    (Finset.le_sup' (fun i => (params i).γ_ℓ) (Finset.mem_range.mpr (Nat.zero_lt_succ m)))
  hK_s := le_trans (params 0).hK_s
    (Finset.le_sup' (fun i => (params i).K_s) (Finset.mem_range.mpr (Nat.zero_lt_succ m)))
  hK_t := le_trans (params 0).hK_t
    (Finset.le_sup' (fun i => (params i).K_t) (Finset.mem_range.mpr (Nat.zero_lt_succ m)))

lemma le_monoSparsifyParamsEnvelope (params : ℕ → SparsifyParams) {m₁ m₂ : ℕ} (h : m₁ ≤ m₂) :
    SparsifyParamsLe (params m₁) (monoSparsifyParamsEnvelope params m₂) := by
  have hm : m₁ ∈ Finset.range (m₂ + 1) := Finset.mem_range.mpr (Nat.lt_succ_of_le h)
  exact ⟨Finset.le_sup' (fun i => (params i).γ_c) hm,
    Finset.le_sup' (fun i => (params i).γ_ℓ) hm,
    Finset.le_sup' (fun i => (params i).K_s) hm,
    Finset.le_sup' (fun i => (params i).p_s) hm,
    Finset.le_sup' (fun i => (params i).K_t) hm,
    Finset.le_sup' (fun i => (params i).p_t) hm⟩

lemma monoSparsifyParamsEnvelope_mono (params : ℕ → SparsifyParams) :
    MonoSparsifyParams (monoSparsifyParamsEnvelope params) := by
  intro m₁ m₂ h
  have hsub : Finset.range (m₁ + 1) ⊆ Finset.range (m₂ + 1) :=
    Finset.range_mono (Nat.add_le_add_right h 1)
  have hne : (Finset.range (m₁ + 1)).Nonempty := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m₁)⟩
  exact ⟨Finset.sup'_mono _ hsub hne, Finset.sup'_mono _ hsub hne, Finset.sup'_mono _ hsub hne,
    Finset.sup'_mono _ hsub hne, Finset.sup'_mono _ hsub hne, Finset.sup'_mono _ hsub hne⟩

lemma monoSparsifyParamsEnvelope_p_s_le (params : ℕ → SparsifyParams) {b : ℕ}
    (h : ∀ m, (params m).p_s ≤ b) (m : ℕ) : (monoSparsifyParamsEnvelope params m).p_s ≤ b :=
  Finset.sup'_le (H := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m)⟩) _ fun i _ => h i

lemma monoSparsifyParamsEnvelope_p_t_le (params : ℕ → SparsifyParams) {b : ℕ}
    (h : ∀ m, (params m).p_t ≤ b) (m : ℕ) : (monoSparsifyParamsEnvelope params m).p_t ≤ b :=
  Finset.sup'_le (H := ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ m)⟩) _ fun i _ => h i

lemma monoSparsifyParamsEnvelope_hp_spec (params : ℕ → SparsifyParams)
    {C_sp K_s K_t : ℝ} (hC : 0 < C_sp)
    (hp_spec : ∀ m : ℕ,
      (params m).K_s = K_s ∧ (params m).p_s = 1 ∧
      (params m).K_t = K_t ∧ (params m).p_t = 1 ∧
      (params m).γ_ℓ ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
      (params m).γ_c ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (m : ℕ) :
    (monoSparsifyParamsEnvelope params m).K_s = K_s ∧
    (monoSparsifyParamsEnvelope params m).p_s = 1 ∧
    (monoSparsifyParamsEnvelope params m).K_t = K_t ∧
    (monoSparsifyParamsEnvelope params m).p_t = 1 ∧
    (monoSparsifyParamsEnvelope params m).γ_ℓ ≤
      Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) ∧
    (monoSparsifyParamsEnvelope params m).γ_c ≤
      Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
  have hmem0 : 0 ∈ Finset.range (m + 1) := Finset.mem_range.mpr (Nat.zero_lt_succ m)
  have hne : (Finset.range (m + 1)).Nonempty := ⟨0, hmem0⟩
  have hexp_mono : ∀ i ∈ Finset.range (m + 1),
      Real.exp (C_sp * Real.log ((i : ℝ) + 2) ^ (7 / 8 : ℝ)) ≤
        Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)) := by
    intro i hi
    have him : (i : ℝ) ≤ (m : ℝ) := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    have hlog_nn : 0 ≤ Real.log ((i : ℝ) + 2) :=
      Real.log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) i])
    have hlog_le : Real.log ((i : ℝ) + 2) ≤ Real.log ((m : ℝ) + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    refine Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left ?_ hC.le)
    exact Real.rpow_le_rpow hlog_nn hlog_le (by norm_num)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact le_antisymm (Finset.sup'_le hne _ fun i _ => (hp_spec i).1.le)
      ((hp_spec 0).1.symm.le.trans (Finset.le_sup' (fun i => (params i).K_s) hmem0))
  · exact le_antisymm (Finset.sup'_le hne _ fun i _ => (hp_spec i).2.1.le)
      ((hp_spec 0).2.1.symm.le.trans (Finset.le_sup' (fun i => (params i).p_s) hmem0))
  · exact le_antisymm (Finset.sup'_le hne _ fun i _ => (hp_spec i).2.2.1.le)
      ((hp_spec 0).2.2.1.symm.le.trans (Finset.le_sup' (fun i => (params i).K_t) hmem0))
  · exact le_antisymm (Finset.sup'_le hne _ fun i _ => (hp_spec i).2.2.2.1.le)
      ((hp_spec 0).2.2.2.1.symm.le.trans (Finset.le_sup' (fun i => (params i).p_t) hmem0))
  · exact Finset.sup'_le hne _ fun i hi => le_trans (hp_spec i).2.2.2.2.1 (hexp_mono i hi)
  · exact Finset.sup'_le hne _ fun i hi => le_trans (hp_spec i).2.2.2.2.2 (hexp_mono i hi)

lemma monoSparsifyParamsEnvelope_sparsifySpec
    (params : ℕ → SparsifyParams)
    (sparsify : MGraph → MGraph → Embedding → SparsifyOut)
    (hSp : ∀ m, SparsifySpec m (params m) sparsify) (m : ℕ) :
    SparsifySpec m (monoSparsifyParamsEnvelope params m) sparsify :=
  sparsifySpec_of_le (le_monoSparsifyParamsEnvelope params le_rfl) (hSp m)

/-! ## 3. Bucket-spanner initialization and batch-update charge bounds -/

/-- Upper bound on the work of initializing a dynamic spanner of depth `L` and split budget
`splitBound` on the bundle graph `Hb` with static sparsifier parameters `P_b`. Covers the static
sparsifier call (with exponent `max p_t 1`), the initial spanner size and bank `O(|E(H₀)|)`,
linear graph work, and the `phaseBase` computation `O((L + 1) log(Hb.n + splitBound + 2))`. -/
noncomputable def spanInitBound (P_b : SparsifyParams) (L splitBound : ℕ) (Hb : MGraph) : ℕ :=
  let Gact := activeSubgraph Hb
  let nMax := Hb.n + splitBound
  ⌈P_b.K_t * (((Gact.n : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ ^ 2) *
      (1 + Real.log ((Gact.n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_b.p_t 1) +
    P_b.K_s * (Hb.n : ℝ) * P_b.γ_ℓ *
      (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_b.p_s +
    (Hb.n : ℝ) + (Hb.m : ℝ) + (Hb.m : ℝ) * P_b.γ_ℓ +
    ((L : ℝ) + 1) * (1 + Real.log ((nMax : ℝ) + 2)) + 1⌉₊

/-- The amortized time bound of Theorem 8.2 per unit of batch encoding size,
`90 L n^{1/L} K₁ E_L Δ₁ Λ`, matching `DynSpanner.Program.dsBatchRate`. -/
noncomputable def spanBatchRate (P_b : SparsifyParams) (L nMax : ℕ) (G₀ : MGraph) : ℝ :=
  90 * (L : ℝ) * ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) * (P_b.K_t + P_b.K_s + 1) *
    (3 ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
      P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2)) * ((G₀.maxDeg : ℝ) + 1) *
    (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ (max P_b.p_s P_b.p_t)

/-- What the sparse-core machine-cost model charges for a dynamic-spanner update batch `U` on
graph `G` in an epoch starting at `G₀` with multiplier `c_sp`:
`⌈c_sp * spanBatchRate P_b L nMax G₀ * G.batchEnc U⌉₊`. At `c_sp = dsAmortConst impl` and
`P_b = (canonicalSparsifyParams impl mMax).absorbTime`, this is definitionally `dsBatchCharge`. -/
noncomputable def spanBatchChargeWith (c_sp : ℕ) (P_b : SparsifyParams) (L nMax : ℕ)
    (G₀ G : MGraph) (U : List Update) : ℕ :=
  ⌈(c_sp : ℝ) * spanBatchRate P_b L nMax G₀ * (G.batchEnc U : ℝ)⌉₊

/-- Specialization of `spanBatchChargeWith` at unit multiplier `c_sp = 1`. -/
noncomputable def spanBatchCharge (P_b : SparsifyParams) (L nMax : ℕ) (G₀ G : MGraph)
    (U : List Update) : ℕ :=
  spanBatchChargeWith 1 P_b L nMax G₀ G U

lemma spanInitBound_graphEq (P_b : SparsifyParams) (L splitBound : ℕ) {G₁ G₂ : MGraph}
    (h : GraphEq G₁ G₂) :
    spanInitBound P_b L splitBound G₁ = spanInitBound P_b L splitBound G₂ := by
  dsimp only [spanInitBound]
  rw [graphEq_activeSubgraph_n h, graphEq_n h, graphEq_m h]

lemma spanInitBound_mono {P₁ P₂ : SparsifyParams} (hP : SparsifyParamsLe P₁ P₂)
    {L s₁ s₂ : ℕ} (hs : s₁ ≤ s₂) (Hb : MGraph) :
    spanInitBound P₁ L s₁ Hb ≤ spanInitBound P₂ L s₂ Hb := by
  dsimp only [spanInitBound]
  refine Nat.ceil_mono ?_
  have hlog1 : (1 : ℝ) ≤ 1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) :=
    one_le_one_add_log_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph Hb).n, Nat.cast_nonneg (α := ℝ) Hb.m])
  have hlog2 : (1 : ℝ) ≤ 1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2) :=
    one_le_one_add_log_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) Hb.n, Nat.cast_nonneg (α := ℝ) Hb.m])
  have hlog3 : Real.log (((Hb.n + s₁ : ℕ) : ℝ) + 2) ≤ Real.log (((Hb.n + s₂ : ℕ) : ℝ) + 2) :=
    Real.log_le_log (by positivity) (by
      have : ((Hb.n + s₁ : ℕ) : ℝ) ≤ ((Hb.n + s₂ : ℕ) : ℝ) := by exact_mod_cast Nat.add_le_add_left hs Hb.n
      linarith)
  have hγ1 : 0 ≤ P₁.γ_ℓ := by linarith [P₁.hγ_ℓ]
  have hγ2 : 0 ≤ P₂.γ_ℓ := by linarith [P₂.hγ_ℓ]
  have hKt1 : 0 ≤ P₁.K_t := P₁.hK_t
  have hKt2 : 0 ≤ P₂.K_t := P₂.hK_t
  have hKs1 : 0 ≤ P₁.K_s := P₁.hK_s
  have hKs2 : 0 ≤ P₂.K_s := P₂.hK_s
  have hpt : max P₁.p_t 1 ≤ max P₂.p_t 1 := max_le_max_right 1 hP.2.2.2.2.2
  have hpow1 := pow_le_pow_right₀ hlog1 hpt
  have hpow2 := pow_le_pow_right₀ hlog2 hP.2.2.2.1
  have hlog1_nn : 0 ≤ 1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) := by linarith
  have hlog2_nn : 0 ≤ 1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2) := by linarith
  have t1 : P₁.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P₁.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P₁.p_t 1) ≤
      P₂.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P₂.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P₂.p_t 1) := by
    have := hP.2.1; have := hP.2.2.2.2.1; gcongr
  have t2 : P₁.K_s * (Hb.n : ℝ) * P₁.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P₁.p_s ≤
      P₂.K_s * (Hb.n : ℝ) * P₂.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P₂.p_s := by
    have := hP.2.1; have := hP.2.2.1; gcongr
  have t3 : (Hb.m : ℝ) * P₁.γ_ℓ ≤ (Hb.m : ℝ) * P₂.γ_ℓ :=
    mul_le_mul_of_nonneg_left hP.2.1 (Nat.cast_nonneg _)
  have t4 : ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + s₁ : ℕ) : ℝ) + 2)) ≤
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + s₂ : ℕ) : ℝ) + 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  linarith

lemma spanInitBound_le_real {P_b P_hi : SparsifyParams} (hP : SparsifyParamsLe P_b P_hi)
    {L splitB M : ℕ} {Hb : MGraph}
    (hnMax : Hb.n + splitB ≤ bundleNMax M) (hm : Hb.m ≤ M) :
    let logN := 1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2)
    let Λ := bundleLambda P_hi M
    (spanInitBound P_b L splitB Hb : ℝ) ≤
      P_hi.K_t * ((Hb.n : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ ^ 2) * (Λ * logN) +
      P_hi.K_s * (Hb.n : ℝ) * P_hi.γ_ℓ * Λ +
      (Hb.n : ℝ) + (Hb.m : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ +
      ((L : ℝ) + 1) * logN + 2 := by
  intro logN Λ
  have hmono : (spanInitBound P_b L splitB Hb : ℝ) ≤ (spanInitBound P_hi L splitB Hb : ℝ) := by
    exact_mod_cast spanInitBound_mono hP le_rfl Hb
  refine le_trans hmono ?_
  have hact_le : ((activeSubgraph Hb).n : ℝ) ≤ (Hb.n : ℝ) := by
    exact_mod_cast activeSubgraph_n_le Hb
  have hn_le_nMax : (Hb.n : ℝ) ≤ (bundleNMax M : ℝ) := by
    exact_mod_cast le_trans (Nat.le_add_right _ _) hnMax
  have hns_le_nMax : ((Hb.n + splitB : ℕ) : ℝ) ≤ (bundleNMax M : ℝ) := by
    exact_mod_cast hnMax
  have hm_le : (Hb.m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm
  have hlogN_ge1 : 1 ≤ logN :=
    one_le_one_add_log_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) (bundleNMax M), Nat.cast_nonneg (α := ℝ) M])
  have hlog_act_le : 1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) ≤ logN := by
    dsimp only [logN]
    have := Real.log_le_log (show (0 : ℝ) < ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2 by positivity)
      (show ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2 ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 by linarith)
    linarith
  have hlog_hb_le : 1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2) ≤ logN := by
    dsimp only [logN]
    have := Real.log_le_log (show (0 : ℝ) < (Hb.n : ℝ) + (Hb.m : ℝ) + 2 by positivity)
      (show (Hb.n : ℝ) + (Hb.m : ℝ) + 2 ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 by linarith)
    linarith
  have hlog_nmax_le : 1 + Real.log (((Hb.n + splitB : ℕ) : ℝ) + 2) ≤ logN := by
    dsimp only [logN]
    have := Real.log_le_log (show (0 : ℝ) < ((Hb.n + splitB : ℕ) : ℝ) + 2 by positivity)
      (show ((Hb.n + splitB : ℕ) : ℝ) + 2 ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 by linarith [Nat.cast_nonneg (α := ℝ) M])
    linarith
  have hlog_act_nn : 0 ≤ 1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2) := by
    have := one_le_one_add_log_of_one_le (x := ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)
      (by linarith [Nat.cast_nonneg (α := ℝ) (activeSubgraph Hb).n, Nat.cast_nonneg (α := ℝ) Hb.m])
    linarith
  have hlog_hb_nn : 0 ≤ 1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2) := by
    have := one_le_one_add_log_of_one_le (x := (Hb.n : ℝ) + (Hb.m : ℝ) + 2)
      (by linarith [Nat.cast_nonneg (α := ℝ) Hb.n, Nat.cast_nonneg (α := ℝ) Hb.m])
    linarith
  have hpow_t : (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_hi.p_t 1 ≤
      Λ * logN := by
    have h1 := pow_le_pow_left₀ hlog_act_nn hlog_act_le (max P_hi.p_t 1)
    have h2 : logN ^ max P_hi.p_t 1 ≤ logN ^ (max P_hi.p_s P_hi.p_t + 1) :=
      pow_le_pow_right₀ hlogN_ge1 (by omega)
    have h3 : logN ^ (max P_hi.p_s P_hi.p_t + 1) = Λ * logN := by
      dsimp only [Λ, bundleLambda, logN]; rw [pow_succ]
    linarith
  have hpow_s : (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_hi.p_s ≤ Λ := by
    have h1 := pow_le_pow_left₀ hlog_hb_nn hlog_hb_le P_hi.p_s
    have h2 : logN ^ P_hi.p_s ≤ Λ :=
      pow_le_pow_right₀ hlogN_ge1 (le_max_left P_hi.p_s P_hi.p_t)
    exact le_trans h1 h2
  have hγ_nn : 0 ≤ P_hi.γ_ℓ := by linarith [P_hi.hγ_ℓ]
  have hKt_nn : 0 ≤ P_hi.K_t := P_hi.hK_t
  have hKs_nn : 0 ≤ P_hi.K_s := P_hi.hK_s
  have hlog3_nn : 0 ≤ 1 + Real.log (((Hb.n + splitB : ℕ) : ℝ) + 2) := by
    have := one_le_one_add_log_of_one_le (x := ((Hb.n + splitB : ℕ) : ℝ) + 2)
      (by linarith [Nat.cast_nonneg (α := ℝ) (Hb.n + splitB)])
    linarith
  have hbody_nn : 0 ≤ P_hi.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_hi.p_t 1) +
      P_hi.K_s * (Hb.n : ℝ) * P_hi.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_hi.p_s +
      (Hb.n : ℝ) + (Hb.m : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ +
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitB : ℕ) : ℝ) + 2)) + 1 := by
    positivity
  have hceil : (spanInitBound P_hi L splitB Hb : ℝ) ≤
      P_hi.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_hi.p_t 1) +
      P_hi.K_s * (Hb.n : ℝ) * P_hi.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_hi.p_s +
      (Hb.n : ℝ) + (Hb.m : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ +
      ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitB : ℕ) : ℝ) + 2)) + 1 + 1 := by
    dsimp only [spanInitBound]
    exact le_of_lt (Nat.ceil_lt_add_one hbody_nn)
  have ht1 : P_hi.K_t * ((((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ ^ 2) *
        (1 + Real.log (((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) + 2)) ^ max P_hi.p_t 1) ≤
      P_hi.K_t * ((Hb.n : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ ^ 2) * (Λ * logN) := by
    have hA : ((activeSubgraph Hb).n : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ ^ 2 ≤
        (Hb.n : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ ^ 2 := by linarith
    have hB := mul_le_mul hA hpow_t (by positivity) (by positivity)
    have hC := mul_le_mul_of_nonneg_left hB hKt_nn
    linarith [show P_hi.K_t * (((Hb.n : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ ^ 2) * (Λ * logN)) =
      P_hi.K_t * ((Hb.n : ℝ) + (Hb.m : ℝ) * P_hi.γ_ℓ ^ 2) * (Λ * logN) by ring]
  have ht2 : P_hi.K_s * (Hb.n : ℝ) * P_hi.γ_ℓ *
        (1 + Real.log ((Hb.n : ℝ) + (Hb.m : ℝ) + 2)) ^ P_hi.p_s ≤
      P_hi.K_s * (Hb.n : ℝ) * P_hi.γ_ℓ * Λ :=
    mul_le_mul_of_nonneg_left hpow_s (by positivity)
  have ht4 : ((L : ℝ) + 1) * (1 + Real.log (((Hb.n + splitB : ℕ) : ℝ) + 2)) ≤
      ((L : ℝ) + 1) * logN :=
    mul_le_mul_of_nonneg_left hlog_nmax_le (by positivity)
  linarith

/-- Sum of `spanInitBound` over a collection of buckets whose total count and total edge count are
at most `M` and whose vertex count satisfies `n ≤ 2 m`. -/
lemma spanInitBound_buckets_sum_le {P_b P_hi : SparsifyParams} (hP : SparsifyParamsLe P_b P_hi)
    {L splitB M : ℕ} (hsplit : splitB ≤ 2 * (56 * M + 1))
    (comps : Finset (Finset ℕ)) (actB : Finset ℕ → Finset ℤ)
    (Hb : Finset ℕ → ℤ → MGraph)
    (hcard : comps.sum (fun C => (actB C).card) ≤ M)
    (hm_sum : comps.sum (fun C => (actB C).sum fun b => (Hb C b).m) ≤ M)
    (hn_le : ∀ C ∈ comps, ∀ b ∈ actB C, (Hb C b).n ≤ 2 * (Hb C b).m) :
    let logN := 1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2)
    let Λ := bundleLambda P_hi M
    ((comps.sum fun C => (actB C).sum fun b =>
        spanInitBound P_b L splitB (Hb C b) : ℕ) : ℝ) ≤
      (P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) * (Λ * logN) +
        2 * P_hi.K_s * P_hi.γ_ℓ * Λ +
        5 + P_hi.γ_ℓ + ((L : ℝ) + 1) * logN) * (M : ℝ) := by
  intro logN Λ
  have hlogN_ge1 : 1 ≤ logN :=
    one_le_one_add_log_of_one_le (by linarith [Nat.cast_nonneg (α := ℝ) (bundleNMax M), Nat.cast_nonneg (α := ℝ) M])
  have hlogN_nn : 0 ≤ logN := by linarith
  have hΛ_nn : 0 ≤ Λ := by dsimp only [Λ, bundleLambda]; exact pow_nonneg hlogN_nn _
  have hγ_nn : 0 ≤ P_hi.γ_ℓ := by linarith [P_hi.hγ_ℓ]
  have hKt_nn : 0 ≤ P_hi.K_t := P_hi.hK_t
  have hKs_nn : 0 ≤ P_hi.K_s := P_hi.hK_s
  have hM_single : ∀ C ∈ comps, ∀ b ∈ actB C, (Hb C b).m ≤ M := fun C hC b hb =>
    le_trans (Finset.single_le_sum (f := fun b' => (Hb C b').m) (fun _ _ => Nat.zero_le _) hb)
      (le_trans (Finset.single_le_sum (f := fun C' => (actB C').sum fun b' => (Hb C' b').m)
        (fun _ _ => Nat.zero_le _) hC) hm_sum)
  have hsingle : ∀ C ∈ comps, ∀ b ∈ actB C,
      (spanInitBound P_b L splitB (Hb C b) : ℝ) ≤
        (P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) * (Λ * logN) +
          2 * P_hi.K_s * P_hi.γ_ℓ * Λ + 3 + P_hi.γ_ℓ) * ((Hb C b).m : ℝ) +
        (((L : ℝ) + 1) * logN + 2) := by
    intro C hC b hb
    have hm := hM_single C hC b hb
    have hn := hn_le C hC b hb
    have hnMax : (Hb C b).n + splitB ≤ bundleNMax M := by
      unfold bundleNMax; omega
    have hraw := spanInitBound_le_real hP hnMax hm (L := L)
    have hnR : ((Hb C b).n : ℝ) ≤ 2 * ((Hb C b).m : ℝ) := by exact_mod_cast hn
    have h1 : P_hi.K_t * (((Hb C b).n : ℝ) + ((Hb C b).m : ℝ) * P_hi.γ_ℓ ^ 2) * (Λ * logN) ≤
        P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) * (Λ * logN) * ((Hb C b).m : ℝ) := by
      have hA : ((Hb C b).n : ℝ) + ((Hb C b).m : ℝ) * P_hi.γ_ℓ ^ 2 ≤
          (2 + P_hi.γ_ℓ ^ 2) * ((Hb C b).m : ℝ) := by linarith
      have hB := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hA hKt_nn) (mul_nonneg hΛ_nn hlogN_nn)
      linarith [show P_hi.K_t * ((2 + P_hi.γ_ℓ ^ 2) * ((Hb C b).m : ℝ)) * (Λ * logN) =
        P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) * (Λ * logN) * ((Hb C b).m : ℝ) by ring]
    have h2 : P_hi.K_s * ((Hb C b).n : ℝ) * P_hi.γ_ℓ * Λ ≤
        2 * P_hi.K_s * P_hi.γ_ℓ * Λ * ((Hb C b).m : ℝ) := by
      have hB := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnR hKs_nn) hγ_nn) hΛ_nn
      linarith [show P_hi.K_s * (2 * ((Hb C b).m : ℝ)) * P_hi.γ_ℓ * Λ =
        2 * P_hi.K_s * P_hi.γ_ℓ * Λ * ((Hb C b).m : ℝ) by ring]
    linarith
  set coeffM : ℝ := P_hi.K_t * (2 + P_hi.γ_ℓ ^ 2) * (Λ * logN) +
    2 * P_hi.K_s * P_hi.γ_ℓ * Λ + 3 + P_hi.γ_ℓ
  set coeff1 : ℝ := ((L : ℝ) + 1) * logN + 2
  have hcoeffM_nn : 0 ≤ coeffM := by dsimp only [coeffM]; positivity
  have hcoeff1_nn : 0 ≤ coeff1 := by dsimp only [coeff1]; positivity
  have hsum_step : ((comps.sum fun C => (actB C).sum fun b =>
        spanInitBound P_b L splitB (Hb C b) : ℕ) : ℝ) ≤
      coeffM * ((comps.sum fun C => (actB C).sum fun b => (Hb C b).m : ℕ) : ℝ) +
      coeff1 * ((comps.sum fun C => (actB C).card : ℕ) : ℝ) := by
    push_cast
    calc ∑ C ∈ comps, ∑ b ∈ actB C, (spanInitBound P_b L splitB (Hb C b) : ℝ)
        ≤ ∑ C ∈ comps, ∑ b ∈ actB C, (coeffM * ((Hb C b).m : ℝ) + coeff1) :=
          Finset.sum_le_sum fun C hC => Finset.sum_le_sum fun b hb => hsingle C hC b hb
      _ = coeffM * (∑ C ∈ comps, ∑ b ∈ actB C, ((Hb C b).m : ℝ)) +
            coeff1 * (∑ C ∈ comps, ((actB C).card : ℝ)) := by
          simp only [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul,
            ← Finset.sum_mul]
          ring
  have hmR : ((comps.sum fun C => (actB C).sum fun b => (Hb C b).m : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hm_sum
  have hcR : ((comps.sum fun C => (actB C).card : ℕ) : ℝ) ≤ (M : ℝ) := by
    exact_mod_cast hcard
  have h1 := mul_le_mul_of_nonneg_left hmR hcoeffM_nn
  have h2 := mul_le_mul_of_nonneg_left hcR hcoeff1_nn
  dsimp only [coeffM, coeff1] at hsum_step h1 h2
  linarith

lemma spanBatchRate_nonneg (P_b : SparsifyParams) (L nMax : ℕ) (G₀ : MGraph) :
    0 ≤ spanBatchRate P_b L nMax G₀ := by
  unfold spanBatchRate
  have h1 : 0 ≤ P_b.γ_c := by linarith [P_b.hγ_c]
  have h2 : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have h3 : 0 ≤ P_b.K_s := P_b.hK_s
  have h4 : 0 ≤ P_b.K_t := P_b.hK_t
  have h5 : 0 ≤ 1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := by
    have := one_le_one_add_log_of_one_le (x := (nMax : ℝ) + (G₀.m : ℝ) + 2)
      (by linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m])
    linarith
  positivity

lemma one_le_spanBatchRate (P_b : SparsifyParams) {L : ℕ} (hL : 1 ≤ L) (nMax : ℕ) (G₀ : MGraph) :
    1 ≤ spanBatchRate P_b L nMax G₀ := by
  unfold spanBatchRate
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hroot : (1 : ℝ) ≤ ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) :=
    Real.one_le_rpow (by exact_mod_cast le_max_right nMax 1) (by positivity)
  have hK : (1 : ℝ) ≤ P_b.K_t + P_b.K_s + 1 := by linarith [P_b.hK_t, P_b.hK_s]
  have h3 : (1 : ℝ) ≤ (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) :=
    one_le_pow₀ (by norm_num)
  have hgc : (1 : ℝ) ≤ P_b.γ_c ^ (L + 1) := one_le_pow₀ P_b.hγ_c
  have hgl : (1 : ℝ) ≤ P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := one_le_pow₀ P_b.hγ_ℓ
  have hE : (1 : ℝ) ≤ (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
      P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le h3 hgc) hgl
  have hd : (1 : ℝ) ≤ (G₀.maxDeg : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) G₀.maxDeg]
  have hlog : (1 : ℝ) ≤ (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t :=
    one_le_pow₀ (one_le_one_add_log_of_one_le
      (by linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m]))
  have h90 : (1 : ℝ) ≤ 90 * (L : ℝ) := by linarith
  exact one_le_mul_of_one_le_of_one_le
    (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le
        (one_le_mul_of_one_le_of_one_le
          (one_le_mul_of_one_le_of_one_le h90 hroot) hK) hE) hd) hlog

lemma spanBatchRate_le {P_b P_hi : SparsifyParams} (hP : SparsifyParamsLe P_b P_hi)
    {L nMax M k : ℕ} {G₀ : MGraph}
    (hn : nMax ≤ bundleNMax M) (hm : G₀.m ≤ M) (hd : G₀.maxDeg ≤ k) :
    spanBatchRate P_b L nMax G₀ ≤
      90 * (L : ℝ) * bundleNRoot L M * (P_hi.K_t + P_hi.K_s + 1) *
        coreE_L L P_hi * ((k : ℝ) + 1) * bundleLambda P_hi M := by
  unfold spanBatchRate bundleNRoot coreE_L bundleLambda
  have hroot : ((max nMax 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) ≤
      ((max (bundleNMax M) 1 : ℕ) : ℝ) ^ (1 / (L : ℝ)) := by
    refine Real.rpow_le_rpow (by positivity) ?_ (by positivity)
    exact_mod_cast max_le_max_right 1 hn
  have hK : P_b.K_t + P_b.K_s + 1 ≤ P_hi.K_t + P_hi.K_s + 1 := by linarith [hP.2.2.1, hP.2.2.2.2.1]
  have hgc0 : 0 ≤ P_b.γ_c := by linarith [P_b.hγ_c]
  have hgl0 : 0 ≤ P_b.γ_ℓ := by linarith [P_b.hγ_ℓ]
  have hgc1 : 0 ≤ P_hi.γ_c := by linarith [P_hi.hγ_c]
  have hgl1 : 0 ≤ P_hi.γ_ℓ := by linarith [P_hi.hγ_ℓ]
  have hKs0 : 0 ≤ P_b.K_s := P_b.hK_s
  have hKt0 : 0 ≤ P_b.K_t := P_b.hK_t
  have hKs1 : 0 ≤ P_hi.K_s := P_hi.hK_s
  have hKt1 : 0 ≤ P_hi.K_t := P_hi.hK_t
  have hE : (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_b.γ_c ^ (L + 1) *
        P_b.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) ≤
      (3 : ℝ) ^ ((L + 1) * (L + 2) / 2 + L + 2) * P_hi.γ_c ^ (L + 1) *
        P_hi.γ_ℓ ^ ((L + 1) * (L + 2) / 2 + 2) := by
    have := hP.1; have := hP.2.1; gcongr
  have hdeg : (G₀.maxDeg : ℝ) + 1 ≤ (k : ℝ) + 1 := by
    have : (G₀.maxDeg : ℝ) ≤ (k : ℝ) := by exact_mod_cast hd
    linarith
  have hlog_nn : 0 ≤ 1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) := by
    have := one_le_one_add_log_of_one_le (x := (nMax : ℝ) + (G₀.m : ℝ) + 2)
      (by linarith [Nat.cast_nonneg (α := ℝ) nMax, Nat.cast_nonneg (α := ℝ) G₀.m])
    linarith
  have hlog_le : 1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2) ≤
      1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2) := by
    have hnR : (nMax : ℝ) ≤ (bundleNMax M : ℝ) := by exact_mod_cast hn
    have hmR : (G₀.m : ℝ) ≤ (M : ℝ) := by exact_mod_cast hm
    linarith [Real.log_le_log (show (0 : ℝ) < (nMax : ℝ) + (G₀.m : ℝ) + 2 by positivity)
      (show (nMax : ℝ) + (G₀.m : ℝ) + 2 ≤ (bundleNMax M : ℝ) + (M : ℝ) + 2 by linarith)]
  have hlog_hi_ge1 : 1 ≤ 1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2) :=
    one_le_one_add_log_of_one_le
      (by linarith [Nat.cast_nonneg (α := ℝ) (bundleNMax M), Nat.cast_nonneg (α := ℝ) M])
  have hlam : (1 + Real.log ((nMax : ℝ) + (G₀.m : ℝ) + 2)) ^ max P_b.p_s P_b.p_t ≤
      (1 + Real.log ((bundleNMax M : ℝ) + (M : ℝ) + 2)) ^ max P_hi.p_s P_hi.p_t :=
    le_trans (pow_le_pow_left₀ hlog_nn hlog_le _)
      (pow_le_pow_right₀ hlog_hi_ge1 (max_le_max hP.2.2.2.1 hP.2.2.2.2.2))
  gcongr

@[simp] lemma spanBatchChargeWith_nil (c_sp : ℕ) (P_b : SparsifyParams) (L nMax : ℕ)
    (G₀ G : MGraph) :
    spanBatchChargeWith c_sp P_b L nMax G₀ G [] = 0 := by
  simp [spanBatchChargeWith, MGraph.batchEnc]

@[simp] lemma spanBatchCharge_nil (P_b : SparsifyParams) (L nMax : ℕ) (G₀ G : MGraph) :
    spanBatchCharge P_b L nMax G₀ G [] = 0 :=
  spanBatchChargeWith_nil 1 P_b L nMax G₀ G

lemma spanBatchChargeWith_graphEq (c_sp : ℕ) (P_b : SparsifyParams) (L nMax : ℕ)
    {G₀ G₀' G G' : MGraph} (h₀ : GraphEq G₀ G₀') (h : GraphEq G G') (U : List Update) :
    spanBatchChargeWith c_sp P_b L nMax G₀ G U = spanBatchChargeWith c_sp P_b L nMax G₀' G' U := by
  unfold spanBatchChargeWith spanBatchRate
  rw [graphEq_maxDeg h₀, graphEq_m h₀, graphEq_batchEnc h]

lemma spanBatchCharge_graphEq (P_b : SparsifyParams) (L nMax : ℕ) {G₀ G₀' G G' : MGraph}
    (h₀ : GraphEq G₀ G₀') (h : GraphEq G G') (U : List Update) :
    spanBatchCharge P_b L nMax G₀ G U = spanBatchCharge P_b L nMax G₀' G' U :=
  spanBatchChargeWith_graphEq 1 P_b L nMax h₀ h U

lemma batchEnc_le_spanBatchChargeWith {c_sp : ℕ} (hc : 1 ≤ c_sp) (P_b : SparsifyParams)
    {L : ℕ} (hL : 1 ≤ L) (nMax : ℕ) (G₀ G : MGraph) (U : List Update) :
    G.batchEnc U ≤ spanBatchChargeWith c_sp P_b L nMax G₀ G U := by
  unfold spanBatchChargeWith
  have hc1 : (1 : ℝ) ≤ (c_sp : ℝ) := by exact_mod_cast hc
  have hr := one_le_spanBatchRate P_b hL nMax G₀
  have hcr : 1 ≤ (c_sp : ℝ) * spanBatchRate P_b L nMax G₀ :=
    one_le_mul_of_one_le_of_one_le hc1 hr
  have hmul : (G.batchEnc U : ℝ) ≤ (c_sp : ℝ) * spanBatchRate P_b L nMax G₀ * (G.batchEnc U : ℝ) := by
    calc (G.batchEnc U : ℝ) = 1 * (G.batchEnc U : ℝ) := (one_mul _).symm
      _ ≤ (c_sp : ℝ) * spanBatchRate P_b L nMax G₀ * (G.batchEnc U : ℝ) :=
        mul_le_mul_of_nonneg_right hcr (Nat.cast_nonneg _)
  exact Nat.le_of_lt_succ (by
    rw [← Nat.cast_lt (α := ℝ)]
    have hceil := Nat.le_ceil ((c_sp : ℝ) * spanBatchRate P_b L nMax G₀ * (G.batchEnc U : ℝ))
    push_cast
    linarith)

lemma batchEnc_le_spanBatchCharge (P_b : SparsifyParams) {L : ℕ} (hL : 1 ≤ L) (nMax : ℕ)
    (G₀ G : MGraph) (U : List Update) :
    G.batchEnc U ≤ spanBatchCharge P_b L nMax G₀ G U :=
  batchEnc_le_spanBatchChargeWith le_rfl P_b hL nMax G₀ G U

lemma spanBatchChargeWith_le_two_mul {c_sp : ℕ} (hc : 1 ≤ c_sp) (P_b : SparsifyParams)
    {L : ℕ} (hL : 1 ≤ L) (nMax : ℕ) (G₀ G : MGraph) (U : List Update) :
    (spanBatchChargeWith c_sp P_b L nMax G₀ G U : ℝ) ≤
      2 * (c_sp : ℝ) * spanBatchRate P_b L nMax G₀ * (G.batchEnc U : ℝ) := by
  by_cases h0 : G.batchEnc U = 0
  · simp [spanBatchChargeWith, h0]
  · have hge1 : (1 : ℝ) ≤ (G.batchEnc U : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero h0
    have hc1 : (1 : ℝ) ≤ (c_sp : ℝ) := by exact_mod_cast hc
    have hr := one_le_spanBatchRate P_b hL nMax G₀
    have hprod_ge1 : 1 ≤ (c_sp : ℝ) * spanBatchRate P_b L nMax G₀ * (G.batchEnc U : ℝ) :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hc1 hr) hge1
    have hceil : (spanBatchChargeWith c_sp P_b L nMax G₀ G U : ℝ) <
        (c_sp : ℝ) * spanBatchRate P_b L nMax G₀ * (G.batchEnc U : ℝ) + 1 :=
      Nat.ceil_lt_add_one (by linarith)
    linarith

lemma spanBatchCharge_le_two_mul (P_b : SparsifyParams) {L : ℕ} (hL : 1 ≤ L) (nMax : ℕ)
    (G₀ G : MGraph) (U : List Update) :
    (spanBatchCharge P_b L nMax G₀ G U : ℝ) ≤
      2 * spanBatchRate P_b L nMax G₀ * (G.batchEnc U : ℝ) := by
  simpa [spanBatchCharge] using spanBatchChargeWith_le_two_mul le_rfl P_b hL nMax G₀ G U

end MinCostFlow.SparseCore
