module

public import MinCostFlow.ExpanderDecomp.MatchingPlayer
public import MinCostFlow.ExpanderDecomp.FakeEdges
public import MinCostFlow.ExpanderDecomp.Rounds
public import MinCostFlow.ExpanderDecomp.BlocksMacro
public import MinCostFlow.ExpanderDecomp.BlockSplit
public import MinCostFlow.ExpanderDecomp.OuterCorePlayer
import MinCostFlow.Expander.GraphHelpers
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.GetD
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Shared parameters, matching completion, and cut padding for `OneShot` and `Core`

This file collects the shared definitions and elementary lemmas used by the one-shot cut player
`OneShot` and the recursive core cut player `Core`:

* `CoreResult`, `CoreParams`, `CoreParamsValid` (with existence lemma `coreParamsValid_exists`),
  `CoreSpec`, and `OneShotSpec`.
* Elementary expansion helpers: monotonicity (`IsExpansionExpanderOn.mono`), permutation invariance
  (`isExpansionExpanderOn_of_perm`), vacuous expansion on `|X| ≤ 1`, and deriving edge expansion
  from conductance plus minimum degree `≥ 1`.
* Matching completion (`completeMatchingFake`, `completeBatchFake`): completing partial matchings
  returned by `RouteOrCut` with fake edges so that each pair becomes a complete injection/bipartite
  matching and the added fake edges form a single matching of size at most the deficit `z`.
* Cut padding (`smallerSide`, `padToHalf`): choosing the smaller side of a cut and padding it to an
  exact bisection of an even-sized block.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-- Abstract parameter schedule for the recursive core up to depth `r`. Concrete instances are
supplied from `Params.lean`. -/
structure CoreParams where
  /-- Branching factor `N` (divisible by `4`). -/
  N : ℕ
  /-- Bit-length parameter `L` with `N ^ r < 2 ^ L`. -/
  L : ℕ
  /-- Degree bound `Δ` for core graphs (e.g. `1024 * L`). -/
  Δ : ℕ
  /-- Inverse expansion parameter `P q` at level `q`. -/
  P : ℕ → ℕ
  /-- Deficit denominator `D q` at level `q`. -/
  D : ℕ → ℕ
  /-- Cloud-expander edge expansion `α` (e.g. `1 / 12`). -/
  α : ℝ

/-- Side conditions on `CoreParams` up to depth `r`, capturing the growth of `P_q` and `D_q`, the bound `N^r < 2^L`, and the
round-bound headroom `49 * L + 20 ≤ Δ`. -/
structure CoreParamsValid (cfg : CoreParams) (r : ℕ) : Prop where
  hNpos : 0 < cfg.N
  hN4 : 4 ∣ cfg.N
  hL : 1 ≤ cfg.L
  hΔ : 49 * cfg.L + 20 ≤ cfg.Δ
  hα0 : 0 < cfg.α
  hα1 : cfg.α ≤ 1
  hP0 : 1 ≤ cfg.P 0
  hPmono : ∀ q < r, cfg.P q ≤ cfg.P (q + 1)
  hP12 : ∀ q, 1 ≤ q → q ≤ r → 12 ≤ cfg.P q
  hPstep : ∀ q, 1 ≤ q → q ≤ r →
    960 * (cfg.P (q - 1) : ℝ) * (cfg.Δ : ℝ) ^ 2 * (routeCong cfg.Δ 100 cfg.L : ℝ) ≤
      cfg.α * (cfg.P q : ℝ)
  hD : ∀ q, 1 ≤ q → q ≤ r → 60 * cfg.Δ * cfg.P q ≤ cfg.D q
  hNrL : cfg.N ^ r < 2 ^ cfg.L

/-- Core-theorem specification for `Core(q, G, X)`: either a balanced sparse cut or a half-size
induced `1 / P_q`-expander. -/
def CoreSpec (cfg : CoreParams) (q : ℕ) (G : Graph) (X : Finset ℕ) : CoreResult → Prop
  | .cut U =>
      U ⊆ X ∧
        X.card ≤ 4 * U.card ∧
        X.card ≤ 4 * (X \ U).card ∧
        100 * G.cutIn X U ≤ X.card
  | .expander S =>
      S ⊆ X ∧
        X.card ≤ 2 * S.card ∧
        G.IsExpansionExpanderOn S (1 / (cfg.P q : ℝ))

/-- Specification for `OneShot(q, G, X)`: either a failed-router cut with sparsity `≤ 1/100`
and both sides `≥ (⌊|X| / D_q⌋ + 1) / 2`, or an induced `1 / P_q`-expander on at least `11/12` of
`X`. -/
def OneShotSpec (cfg : CoreParams) (q : ℕ) (G : Graph) (X : Finset ℕ) : CoreResult → Prop
  | .cut U => RouteCutSpec G X 100 (X.card / cfg.D q) U
  | .expander R =>
      R ⊆ X ∧
        11 * X.card ≤ 12 * R.card ∧
        G.IsExpansionExpanderOn R (1 / (cfg.P q : ℝ))

/-- Unmatched vertices of `A` with respect to the first endpoints of `M`, in sorted order. -/
def unmatchedFst (A : Finset ℕ) (M : List (ℕ × ℕ)) : List ℕ :=
  (A \ (M.map Prod.fst).toFinset).sort (· ≤ ·)

/-- Unmatched vertices of `B` with respect to the second endpoints of `M`, in sorted order. -/
def unmatchedSnd (B : Finset ℕ) (M : List (ℕ × ℕ)) : List ℕ :=
  (B \ (M.map Prod.snd).toFinset).sort (· ≤ ·)

/-- Fake edges completing a partial matching `M ⊆ A × B` into an injection from `A` into `B`. -/
def completeMatchingFake (A B : Finset ℕ) (M : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (unmatchedFst A M).zip (unmatchedSnd B M)

/-- Fake edges completing every partial matching in a multi-pair routing batch. -/
def completeBatchFake (pairs : List (Finset ℕ × Finset ℕ))
    (matchings : List (List (ℕ × ℕ))) : List (ℕ × ℕ) :=
  (List.zipWith (fun p M => completeMatchingFake p.1 p.2 M) pairs matchings).flatten

/-- Choose the smaller side of a cut `U ⊆ B`. -/
def smallerSide (B U : Finset ℕ) : Finset ℕ :=
  if U.card ≤ (B \ U).card then U else B \ U

/-- Pad a subset `C ⊆ B` with `2 * |C| ≤ |B|` to an exact half-set of size `|B| / 2`. -/
def padToHalf (B C : Finset ℕ) : Finset ℕ :=
  C ∪ (((B \ C).sort (· ≤ ·)).take (B.card / 2 - C.card)).toFinset

/-- Record of one successful routing call: the routed witness edges, their host embedding, and the
fake edges added to complete the call's matchings. -/
structure RoutedCall where
  routed : List (ℕ × ℕ)
  emb : ℕ → List ℕ
  fake : List (ℕ × ℕ)

/-- Validity of a `RoutedCall` against host `G[X]`, congestion bound `R`, and deficit budget `z`. -/
def RoutedCall.Valid (G : Graph) (X : Finset ℕ) (R z : ℕ) (c : RoutedCall) : Prop :=
  (∀ e ∈ c.routed, e.1 ∈ X ∧ e.2 ∈ X) ∧
    IsEmbeddingOn (Graph.mk G.n c.routed) G X c.emb ∧
    (∀ i < G.m, congestion (Graph.mk G.n c.routed) c.emb i ≤ R) ∧
    (∀ e ∈ c.fake, e.1 ∈ X ∧ e.2 ∈ X) ∧
    (c.fake.flatMap fun e => [e.1, e.2]).Nodup ∧
    c.fake.length ≤ z

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Existence of valid `CoreParams` and basic parameter consequences -/

/-- `CoreParamsValid` is non-vacuous for every depth `r`. -/
theorem coreParamsValid_exists (r : ℕ) : ∃ cfg : CoreParams, CoreParamsValid cfg r := by
  let N := 4
  let L := 2 * r + 1
  let Δ := 49 * L + 20
  let F := 960 * Δ ^ 2 * routeCong Δ 100 L + 12
  let P : ℕ → ℕ := fun q => F ^ q
  let D : ℕ → ℕ := fun q => 60 * Δ * P q
  refine ⟨⟨N, L, Δ, P, D, 1⟩, ?_⟩
  have hF12 : 12 ≤ F := Nat.le_add_left 12 _
  have hF1 : 1 ≤ F := le_trans (by decide : 1 ≤ 12) hF12
  refine ⟨by show 0 < 4; omega, dvd_refl 4, by show 1 ≤ 2 * r + 1; omega, le_refl _, zero_lt_one, le_refl _, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp [P]
  · intro q _
    show F ^ q ≤ F ^ (q + 1)
    rw [pow_succ]
    exact Nat.le_mul_of_pos_right _ hF1
  · intro q hq _
    show 12 ≤ F ^ q
    calc 12 ≤ F := hF12
      _ = F ^ 1 := (pow_one F).symm
      _ ≤ F ^ q := Nat.pow_le_pow_right hF1 hq
  · intro q hq _
    dsimp only
    rw [one_mul]
    have hsplit : P q = P (q - 1) * F := by
      show F ^ q = F ^ (q - 1) * F
      conv_lhs => rw [show q = (q - 1) + 1 by omega, pow_succ]
    rw [hsplit]
    have hFge : 960 * Δ ^ 2 * routeCong Δ 100 L ≤ F := Nat.le_add_right _ 12
    have hnat : 960 * P (q - 1) * Δ ^ 2 * routeCong Δ 100 L ≤ P (q - 1) * F := by
      calc 960 * P (q - 1) * Δ ^ 2 * routeCong Δ 100 L
          = P (q - 1) * (960 * Δ ^ 2 * routeCong Δ 100 L) := by ring
        _ ≤ P (q - 1) * F := Nat.mul_le_mul_left _ hFge
    exact_mod_cast hnat
  · intro q _ _
    exact le_refl _
  · show 4 ^ r < 2 ^ (2 * r + 1)
    have h4 : 4 ^ r = 2 ^ (2 * r) := by
      rw [show (4 : ℕ) = 2 ^ 2 by decide, ← pow_mul]
    rw [h4]
    exact Nat.pow_lt_pow_right (by decide) (by omega)

theorem CoreParamsValid.hΔ_pos {cfg : CoreParams} {r : ℕ} (h : CoreParamsValid cfg r) :
    1 ≤ cfg.Δ := by
  have := h.hL; have := h.hΔ; omega

theorem CoreParamsValid.hP_pos {cfg : CoreParams} {r : ℕ} (h : CoreParamsValid cfg r)
    {q : ℕ} (hq : q ≤ r) : 1 ≤ cfg.P q := by
  induction q with
  | zero => exact h.hP0
  | succ q ih =>
    exact le_trans (ih (Nat.le_of_succ_le hq)) (h.hPmono q hq)

theorem CoreParamsValid.hP_le_of_le {cfg : CoreParams} {r : ℕ} (h : CoreParamsValid cfg r)
    {q₁ q₂ : ℕ} (h12 : q₁ ≤ q₂) (h2r : q₂ ≤ r) : cfg.P q₁ ≤ cfg.P q₂ := by
  induction h12 with
  | refl => exact le_refl _
  | step hle ih => exact le_trans (ih (Nat.le_of_succ_le h2r)) (h.hPmono _ h2r)

theorem CoreParamsValid.hD_pos {cfg : CoreParams} {r : ℕ} (h : CoreParamsValid cfg r)
    {q : ℕ} (hq1 : 1 ≤ q) (hqr : q ≤ r) : 1 ≤ cfg.D q := by
  have h1 := h.hD q hq1 hqr
  have hΔ := h.hΔ_pos
  have hP := h.hP_pos hqr
  have hmul : 1 ≤ 60 * cfg.Δ * cfg.P q := by
    calc 1 = 1 * 1 * 1 := by norm_num
      _ ≤ 60 * cfg.Δ * cfg.P q := Nat.mul_le_mul (Nat.mul_le_mul (by omega) hΔ) hP
  omega

theorem CoreParamsValid.hNq_lt_two_pow {cfg : CoreParams} {r : ℕ} (h : CoreParamsValid cfg r)
    {q : ℕ} (hq : q ≤ r) : cfg.N ^ q < 2 ^ cfg.L := by
  calc cfg.N ^ q ≤ cfg.N ^ r := Nat.pow_le_pow_right h.hNpos hq
    _ < 2 ^ cfg.L := h.hNrL

theorem CoreParamsValid.routeCong_pos {cfg : CoreParams} {r : ℕ} (h : CoreParamsValid cfg r) :
    1 ≤ routeCong cfg.Δ 100 cfg.L := by
  unfold routeCong routeBatchH routePathLen
  have hΔ := h.hΔ_pos
  have hL := h.hL
  have h1 : 1 ≤ 16 * 100 * cfg.Δ := by omega
  have h2 : 1 ≤ 32 * cfg.Δ * 100 * cfg.L + 1 := by omega
  calc 1 = 1 * 1 * 1 := by norm_num
    _ ≤ 16 * 100 * cfg.Δ * (32 * cfg.Δ * 100 * cfg.L + 1) * cfg.L :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2) hL

/-! ### Elementary expansion lemmas -/

/-- Lowering the expansion parameter preserves `IsExpansionExpanderOn`. -/
theorem IsExpansionExpanderOn.mono {G : Graph} {X : Finset ℕ} {ψ₁ ψ₂ : ℝ}
    (hψ : ψ₁ ≤ ψ₂) (h : G.IsExpansionExpanderOn X ψ₂) :
    G.IsExpansionExpanderOn X ψ₁ := by
  intro S hSX hne hneX
  have h2 := h S hSX hne hneX
  have hmin : 0 ≤ min (S.card : ℝ) ((X \ S).card : ℝ) :=
    le_min (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  exact le_trans (mul_le_mul_of_nonneg_right hψ hmin) h2

/-- Permuting the edge list preserves `IsExpansionExpanderOn`. -/
theorem isExpansionExpanderOn_of_perm {n : ℕ} {E₁ E₂ : List (ℕ × ℕ)} (hp : E₁.Perm E₂)
    {X : Finset ℕ} {ψ : ℝ} (h : (Graph.mk n E₁).IsExpansionExpanderOn X ψ) :
    (Graph.mk n E₂).IsExpansionExpanderOn X ψ := by
  intro S hSX hne hneX
  rw [← cutIn_of_perm n hp X S]
  exact h S hSX hne hneX

/-- Any graph vacuously expands on a set of size at most `1`. -/
theorem isExpansionExpanderOn_of_card_le_one (G : Graph) {X : Finset ℕ}
    (hX : X.card ≤ 1) (ψ : ℝ) : G.IsExpansionExpanderOn X ψ := by
  intro S hSX hne hneX
  exfalso
  have h1 : 1 ≤ S.card := hne.card_pos
  have h2 : S.card ≤ X.card := Finset.card_le_card hSX
  exact hneX (Finset.eq_of_subset_of_card_le hSX (by omega))

/-- Conductance `φ ≥ 0` plus minimum degree at least `1` implies edge expansion `φ`. -/
theorem isExpansionExpanderOn_of_conductance_minDeg {G : Graph} {X : Finset ℕ} {φ : ℝ}
    (hφ : 0 ≤ φ) (hcond : G.IsConductanceExpanderOn X φ)
    (hdeg : ∀ v ∈ X, 1 ≤ G.degIn X v) :
    G.IsExpansionExpanderOn X φ := by
  intro S hSX hne hneX
  have hc := hcond S hSX hne hneX
  have hv1 : (S.card : ℝ) ≤ G.volIn X S := by
    exact_mod_cast card_le_volIn fun v hv => hdeg v (hSX hv)
  have hv2 : ((X \ S).card : ℝ) ≤ G.volIn X (X \ S) := by
    exact_mod_cast card_le_volIn fun v hv => hdeg v (Finset.sdiff_subset hv)
  have hmin : min (S.card : ℝ) ((X \ S).card : ℝ) ≤
      min (G.volIn X S : ℝ) (G.volIn X (X \ S) : ℝ) := min_le_min hv1 hv2
  exact le_trans (mul_le_mul_of_nonneg_left hmin hφ) hc

/-! ### Completing partial matchings with fake edges -/

private lemma mem_unmatchedFst_iff {A : Finset ℕ} {M : List (ℕ × ℕ)} {v : ℕ} :
    v ∈ unmatchedFst A M ↔ v ∈ A ∧ v ∉ M.map Prod.fst := by
  unfold unmatchedFst
  rw [Finset.mem_sort, Finset.mem_sdiff, List.mem_toFinset]

private lemma mem_unmatchedSnd_iff {B : Finset ℕ} {M : List (ℕ × ℕ)} {v : ℕ} :
    v ∈ unmatchedSnd B M ↔ v ∈ B ∧ v ∉ M.map Prod.snd := by
  unfold unmatchedSnd
  rw [Finset.mem_sort, Finset.mem_sdiff, List.mem_toFinset]

private lemma map_snd_zip_sublist' {α β : Type*} (l₁ : List α) (l₂ : List β) :
    List.Sublist ((l₁.zip l₂).map Prod.snd) l₂ := by
  induction l₁ generalizing l₂ with
  | nil => simp
  | cons a t ih =>
    cases l₂ with
    | nil => simp
    | cons b s =>
      simp only [List.zip_cons_cons, List.map_cons]
      exact List.Sublist.cons_cons b (ih s)

/-- Full specification of `completeMatchingFake A B M` for a partial matching `M ⊆ A × B` with
`|A| ≤ |B|`. -/
theorem completeMatchingFake_spec {A B : Finset ℕ} {M : List (ℕ × ℕ)}
    (hAB : A.card ≤ B.card)
    (hmem : ∀ e ∈ M, e.1 ∈ A ∧ e.2 ∈ B)
    (hfst : (M.map Prod.fst).Nodup) (hsnd : (M.map Prod.snd).Nodup) :
    let F := completeMatchingFake A B M
    F.length = A.card - M.length ∧
    (∀ e ∈ F, e.1 ∈ A ∧ e.2 ∈ B) ∧
    (F.map Prod.fst).Nodup ∧
    (F.map Prod.snd).Nodup ∧
    ((M ++ F).map Prod.fst).Nodup ∧
    ((M ++ F).map Prod.snd).Nodup ∧
    (M ++ F).length = A.card ∧
    (∀ u ∈ A, ∃ e ∈ M ++ F, e.1 = u) := by
  dsimp only
  have hsubA : (M.map Prod.fst).toFinset ⊆ A := by
    intro u hu
    rw [List.mem_toFinset, List.mem_map] at hu
    obtain ⟨e, he, rfl⟩ := hu
    exact (hmem e he).1
  have hsubB : (M.map Prod.snd).toFinset ⊆ B := by
    intro u hu
    rw [List.mem_toFinset, List.mem_map] at hu
    obtain ⟨e, he, rfl⟩ := hu
    exact (hmem e he).2
  have hcard1 : (M.map Prod.fst).toFinset.card = M.length := by
    rw [List.toFinset_card_of_nodup hfst, List.length_map]
  have hcard2 : (M.map Prod.snd).toFinset.card = M.length := by
    rw [List.toFinset_card_of_nodup hsnd, List.length_map]
  have hMleA : M.length ≤ A.card := hcard1 ▸ Finset.card_le_card hsubA
  have hlen1 : (unmatchedFst A M).length = A.card - M.length := by
    unfold unmatchedFst
    rw [Finset.length_sort, Finset.card_sdiff_of_subset hsubA, hcard1]
  have hlen2 : (unmatchedSnd B M).length = B.card - M.length := by
    unfold unmatchedSnd
    rw [Finset.length_sort, Finset.card_sdiff_of_subset hsubB, hcard2]
  have hlen_le : (unmatchedFst A M).length ≤ (unmatchedSnd B M).length := by omega
  have hFlen : (completeMatchingFake A B M).length = A.card - M.length := by
    unfold completeMatchingFake
    rw [List.length_zip, Nat.min_eq_left hlen_le, hlen1]
  have hFmem : ∀ e ∈ completeMatchingFake A B M, e.1 ∈ A ∧ e.2 ∈ B := by
    intro e he
    have h1 := mem_unmatchedFst_iff.mp (List.of_mem_zip he).1
    have h2 := mem_unmatchedSnd_iff.mp (List.of_mem_zip he).2
    exact ⟨h1.1, h2.1⟩
  have hFmap1 : (completeMatchingFake A B M).map Prod.fst = unmatchedFst A M := by
    unfold completeMatchingFake
    exact List.map_fst_zip hlen_le
  have hFnd1 : ((completeMatchingFake A B M).map Prod.fst).Nodup := by
    rw [hFmap1]
    exact Finset.sort_nodup _ _
  have hFnd2 : ((completeMatchingFake A B M).map Prod.snd).Nodup := by
    unfold completeMatchingFake
    exact (map_snd_zip_sublist' _ _).nodup (Finset.sort_nodup _ _)
  have hMFnd1 : ((M ++ completeMatchingFake A B M).map Prod.fst).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨hfst, hFnd1, fun u huM v hvF heq => ?_⟩
    subst heq
    rw [hFmap1, mem_unmatchedFst_iff] at hvF
    exact hvF.2 huM
  have hMFnd2 : ((M ++ completeMatchingFake A B M).map Prod.snd).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨hsnd, hFnd2, fun u huM v hvF heq => ?_⟩
    subst heq
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hvF
    exact (mem_unmatchedSnd_iff.mp (List.of_mem_zip he).2).2 huM
  have hMFlen : (M ++ completeMatchingFake A B M).length = A.card := by
    rw [List.length_append, hFlen]
    omega
  have hcov : ∀ u ∈ A, ∃ e ∈ M ++ completeMatchingFake A B M, e.1 = u := by
    intro u huA
    by_cases huM : u ∈ M.map Prod.fst
    · obtain ⟨e, he, rfl⟩ := List.mem_map.mp huM
      exact ⟨e, List.mem_append_left _ he, rfl⟩
    · have huF : u ∈ (completeMatchingFake A B M).map Prod.fst := by
        rw [hFmap1, mem_unmatchedFst_iff]
        exact ⟨huA, huM⟩
      obtain ⟨e, he, rfl⟩ := List.mem_map.mp huF
      exact ⟨e, List.mem_append_right _ he, rfl⟩
  exact ⟨hFlen, hFmem, hFnd1, hFnd2, hMFnd1, hMFnd2, hMFlen, hcov⟩

/-- When `|A| = |B|` and `Disjoint A B`, `M ++ completeMatchingFake A B M` is a bipartite perfect
matching between `A` and `B`. -/
theorem isBipartiteMatching_complete {A B : Finset ℕ} {M : List (ℕ × ℕ)}
    (hdisj : Disjoint A B) (heq : A.card = B.card)
    (hmem : ∀ e ∈ M, e.1 ∈ A ∧ e.2 ∈ B)
    (hfst : (M.map Prod.fst).Nodup) (hsnd : (M.map Prod.snd).Nodup) :
    IsBipartiteMatching A B (M ++ completeMatchingFake A B M) := by
  have hs := completeMatchingFake_spec (le_of_eq heq) hmem hfst hsnd
  refine IsBipartiteMatching.of_directed hdisj ?_ hs.2.2.2.2.1 hs.2.2.2.2.2.1
    hs.2.2.2.2.2.2.1 (hs.2.2.2.2.2.2.1.trans heq)
  intro e he
  rcases List.mem_append.mp he with h | h
  · exact hmem e h
  · exact hs.2.1 e h

/-- When `A ∪ B = V`, `|A| = |B|`, and `Disjoint A B`, `M ++ completeMatchingFake A B M` is a
perfect matching on `V`. -/
theorem isPerfectMatchingOn_complete {V A B : Finset ℕ} {M : List (ℕ × ℕ)}
    (hdisj : Disjoint A B) (hunion : A ∪ B = V) (heq : A.card = B.card)
    (hmem : ∀ e ∈ M, e.1 ∈ A ∧ e.2 ∈ B)
    (hfst : (M.map Prod.fst).Nodup) (hsnd : (M.map Prod.snd).Nodup) :
    IsPerfectMatchingOn V (M ++ completeMatchingFake A B M) := by
  have hbip := isBipartiteMatching_complete hdisj heq hmem hfst hsnd
  have hs := completeMatchingFake_spec (le_of_eq heq) hmem hfst hsnd
  set M' := M ++ completeMatchingFake A B M
  refine ⟨?_, hbip.2.1, ?_⟩
  · intro e he
    rw [← hunion]
    rcases hbip.1 e he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨Finset.mem_union_left _ h1, Finset.mem_union_right _ h2⟩
    · exact ⟨Finset.mem_union_right _ h1, Finset.mem_union_left _ h2⟩
  · intro u hu
    rw [← hunion, Finset.mem_union] at hu
    rcases hu with huA | huB
    · obtain ⟨e, he, rfl⟩ := hs.2.2.2.2.2.2.2 u huA
      exact ⟨e, he, Or.inl rfl⟩
    · have hsub : (M'.map Prod.snd).toFinset ⊆ B := by
        intro w hw
        rw [List.mem_toFinset, List.mem_map] at hw
        obtain ⟨e, he, rfl⟩ := hw
        rcases List.mem_append.mp he with h | h
        · exact (hmem e h).2
        · exact (hs.2.1 e h).2
      have hcard : (M'.map Prod.snd).toFinset.card = B.card := by
        rw [List.toFinset_card_of_nodup hs.2.2.2.2.2.1, List.length_map, hs.2.2.2.2.2.2.1, heq]
      have hset : (M'.map Prod.snd).toFinset = B :=
        Finset.eq_of_subset_of_card_le hsub (le_of_eq hcard.symm)
      rw [← hset, List.mem_toFinset, List.mem_map] at huB
      obtain ⟨e, he, rfl⟩ := huB
      exact ⟨e, he, Or.inr rfl⟩

/-- Converting a `RouteMatchedSpec` outcome into a valid `RoutedCall` via `completeBatchFake`. -/
theorem routedCall_valid_of_matched {G : Graph} {X : Finset ℕ}
    {pairs : List (Finset ℕ × Finset ℕ)} {Δ L b z : ℕ}
    {matchings : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hpairs : ValidTerminalPairs X pairs)
    (hspec : RouteMatchedSpec G X pairs Δ L b z matchings emb) :
    RoutedCall.Valid G X (routeCong Δ b L) z
      ⟨matchings.flatten, emb, completeBatchFake pairs matchings⟩ := by
  obtain ⟨hlen, hpair_spec, hdef, hemb, _, hcong⟩ := hspec
  have hbatch : ∀ (ps : List (Finset ℕ × Finset ℕ)) (ms : List (List (ℕ × ℕ))),
      ValidTerminalPairs X ps →
      ms.length = ps.length →
      (∀ i (hi : i < ps.length),
        let M := ms.getD i []
        let p := ps[i]'hi
        (∀ e ∈ M, e.1 ∈ p.1 ∧ e.2 ∈ p.2) ∧
          (M.map Prod.fst).Nodup ∧ (M.map Prod.snd).Nodup) →
      (∀ e ∈ completeBatchFake ps ms, e.1 ∈ X ∧ e.2 ∈ X) ∧
      ((completeBatchFake ps ms).flatMap fun e => [e.1, e.2]).Nodup ∧
      (completeBatchFake ps ms).length =
        (List.zipWith (fun p M => p.1.card - M.length) ps ms).sum ∧
      (∀ e ∈ completeBatchFake ps ms, ∃ p ∈ ps, e.1 ∈ p.1 ∧ e.2 ∈ p.2) := by
    intro ps
    induction ps with
    | nil =>
      intro ms _ hml _
      cases ms with
      | nil => simp [completeBatchFake]
      | cons _ _ => simp at hml
    | cons p prest ih =>
      intro ms hvp hml hms
      cases ms with
      | nil => simp at hml
      | cons m mrest =>
        have hvp_rest : ValidTerminalPairs X prest := by
          refine ⟨fun q hq => hvp.1 q (List.mem_cons_of_mem _ hq), ?_⟩
          have hpw := hvp.2
          simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.pairwise_cons] at hpw
          exact hpw.2.2
        have hml_rest : mrest.length = prest.length := by simpa using hml
        have hms_rest : ∀ i (hi : i < prest.length),
            let M := mrest.getD i []
            let q := prest[i]'hi
            (∀ e ∈ M, e.1 ∈ q.1 ∧ e.2 ∈ q.2) ∧
              (M.map Prod.fst).Nodup ∧ (M.map Prod.snd).Nodup := by
          intro i hi
          have h := hms (i + 1) (Nat.succ_lt_succ hi)
          simpa [List.getD_cons_succ] using h
        have hhead := hms 0 (Nat.zero_lt_succ _)
        simp only [List.getD_cons_zero, List.getElem_cons_zero] at hhead
        have hp_valid := hvp.1 p List.mem_cons_self
        have hp_disj := hvp.disjoint_pair List.mem_cons_self
        have hF0 := completeMatchingFake_spec hp_valid.2.2 hhead.1 hhead.2.1 hhead.2.2
        have hF0_nd : ((completeMatchingFake p.1 p.2 m).flatMap fun e => [e.1, e.2]).Nodup := by
          have hnd_dir : ∀ (l : List (ℕ × ℕ)),
              (∀ e ∈ l, e.1 ∈ p.1 ∧ e.2 ∈ p.2) →
              (l.map Prod.fst).Nodup → (l.map Prod.snd).Nodup →
              (l.flatMap fun e => [e.1, e.2]).Nodup := by
            intro l
            induction l with
            | nil => intro _ _ _; simp
            | cons e rest ihl =>
              intro hl hf hs
              simp only [List.map_cons, List.nodup_cons] at hf hs
              have he := hl e List.mem_cons_self
              have hrest : ∀ e' ∈ rest, e'.1 ∈ p.1 ∧ e'.2 ∈ p.2 :=
                fun e' he' => hl e' (List.mem_cons_of_mem _ he')
              simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons]
              refine ⟨?_, ?_, ihl hrest hf.2 hs.2⟩
              · intro hmem
                rcases List.mem_cons.mp hmem with h12 | hfm
                · exact Finset.disjoint_left.mp hp_disj he.1 (h12 ▸ he.2)
                · obtain ⟨e', he', hm⟩ := List.mem_flatMap.mp hfm
                  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
                  rcases hm with h | h
                  · exact hf.1 (List.mem_map.mpr ⟨e', he', h.symm⟩)
                  · exact Finset.disjoint_left.mp hp_disj he.1 (h ▸ (hrest e' he').2)
              · intro hmem
                obtain ⟨e', he', hm⟩ := List.mem_flatMap.mp hmem
                simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
                rcases hm with h | h
                · exact Finset.disjoint_left.mp hp_disj (hrest e' he').1 (h ▸ he.2)
                · exact hs.1 (List.mem_map.mpr ⟨e', he', h.symm⟩)
          exact hnd_dir _ hF0.2.1 hF0.2.2.1 hF0.2.2.2.1
        obtain ⟨hr_mem, hr_nd, hr_len, hr_pair⟩ := ih mrest hvp_rest hml_rest hms_rest
        have hcb : completeBatchFake (p :: prest) (m :: mrest) =
            completeMatchingFake p.1 p.2 m ++ completeBatchFake prest mrest := by
          simp [completeBatchFake]
        rw [hcb]
        refine ⟨?_, ?_, ?_, ?_⟩
        · intro e he
          rcases List.mem_append.mp he with h | h
          · exact ⟨hp_valid.1 (hF0.2.1 e h).1, hp_valid.2.1 (hF0.2.1 e h).2⟩
          · exact hr_mem e h
        · rw [List.flatMap_append, List.nodup_append]
          refine ⟨hF0_nd, hr_nd, fun u hu0 v huv heq => ?_⟩
          subst heq
          obtain ⟨e₀, he₀, hu₀⟩ := List.mem_flatMap.mp hu0
          obtain ⟨e₁, he₁, hu₁⟩ := List.mem_flatMap.mp huv
          obtain ⟨q, hq, hq1, hq2⟩ := hr_pair e₁ he₁
          have hpw := hvp.2
          simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.pairwise_cons] at hpw
          have hq1_mem : q.1 ∈ prest.flatMap fun x => [x.1, x.2] :=
            List.mem_flatMap.mpr ⟨q, hq, by simp⟩
          have hq2_mem : q.2 ∈ prest.flatMap fun x => [x.1, x.2] :=
            List.mem_flatMap.mpr ⟨q, hq, by simp⟩
          have hd11 : Disjoint p.1 q.1 := hpw.1 q.1 (List.mem_cons_of_mem _ hq1_mem)
          have hd12 : Disjoint p.1 q.2 := hpw.1 q.2 (List.mem_cons_of_mem _ hq2_mem)
          have hd21 : Disjoint p.2 q.1 := hpw.2.1 q.1 hq1_mem
          have hd22 : Disjoint p.2 q.2 := hpw.2.1 q.2 hq2_mem
          simp only [List.mem_cons, List.not_mem_nil, or_false] at hu₀ hu₁
          have hp0 := hF0.2.1 e₀ he₀
          rcases hu₀ with rfl | rfl <;> rcases hu₁ with h | h
          · exact Finset.disjoint_left.mp hd11 hp0.1 (h ▸ hq1)
          · exact Finset.disjoint_left.mp hd12 hp0.1 (h ▸ hq2)
          · exact Finset.disjoint_left.mp hd21 hp0.2 (h ▸ hq1)
          · exact Finset.disjoint_left.mp hd22 hp0.2 (h ▸ hq2)
        · rw [List.length_append, hF0.1, hr_len, List.zipWith_cons_cons, List.sum_cons]
        · intro e he
          rcases List.mem_append.mp he with h | h
          · exact ⟨p, List.mem_cons_self, hF0.2.1 e h⟩
          · obtain ⟨q, hq, hq1, hq2⟩ := hr_pair e h
            exact ⟨q, List.mem_cons_of_mem _ hq, hq1, hq2⟩
  obtain ⟨hf_mem, hf_nd, hf_len, _⟩ := hbatch pairs matchings hpairs hlen hpair_spec
  have hrouted_mem : ∀ e ∈ matchings.flatten, e.1 ∈ X ∧ e.2 ∈ X := by
    intro e he
    obtain ⟨M, hM, heM⟩ := List.mem_flatten.mp he
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hM
    have hi' : i < pairs.length := hlen ▸ hi
    have hsp := hpair_spec i hi'
    dsimp only at hsp
    have hget : matchings.getD i [] = matchings[i]'hi := List.getD_eq_getElem matchings [] hi
    rw [hget] at hsp
    have hvp := hpairs.1 (pairs[i]'hi') (List.getElem_mem hi')
    exact ⟨hvp.1 (hsp.1 e heM).1, hvp.2.1 (hsp.1 e heM).2⟩
  exact ⟨hrouted_mem, hemb, hcong, hf_mem, hf_nd, hf_len ▸ hdef⟩

/-! ### Cut padding for Step B -/

theorem smallerSide_spec {G : Graph} {B U : Finset ℕ} (hUB : U ⊆ B)
    (h1 : B.card ≤ 4 * U.card) (h2 : B.card ≤ 4 * (B \ U).card)
    (hcut : 100 * G.cutIn B U ≤ B.card) :
    let C := smallerSide B U
    C ⊆ B ∧ 2 * C.card ≤ B.card ∧ B.card ≤ 4 * C.card ∧ 100 * G.cutIn B C ≤ B.card := by
  dsimp only
  unfold smallerSide
  have hadd : (B \ U).card + U.card = B.card := Finset.card_sdiff_add_card_eq_card hUB
  by_cases hle : U.card ≤ (B \ U).card
  · simp only [hle, ↓reduceIte]
    exact ⟨hUB, by omega, h1, hcut⟩
  · simp only [hle, ↓reduceIte]
    rw [cutIn_sdiff G B U hUB]
    exact ⟨Finset.sdiff_subset, by omega, h2, hcut⟩

theorem padToHalf_spec {B C : Finset ℕ} (hCB : C ⊆ B) (h2C : 2 * C.card ≤ B.card)
    (heven : Even B.card) :
    let C' := padToHalf B C
    C ⊆ C' ∧ C' ⊆ B ∧ C'.card = B.card / 2 ∧ (B \ C').card = C'.card := by
  dsimp only
  unfold padToHalf
  set pad := (((B \ C).sort (· ≤ ·)).take (B.card / 2 - C.card)).toFinset
  have hpad_sub : pad ⊆ B \ C := by
    intro v hv
    rw [List.mem_toFinset] at hv
    exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take hv)
  have hdisj : Disjoint C pad :=
    Finset.disjoint_of_subset_right hpad_sub disjoint_sdiff_self_right
  have hsd_card : (B \ C).card = B.card - C.card := Finset.card_sdiff_of_subset hCB
  have htake_le : B.card / 2 - C.card ≤ ((B \ C).sort (· ≤ ·)).length := by
    rw [Finset.length_sort, hsd_card]
    omega
  have hpad_card : pad.card = B.card / 2 - C.card := by
    have hnd : (((B \ C).sort (· ≤ ·)).take (B.card / 2 - C.card)).Nodup :=
      (List.take_sublist _ _).nodup (Finset.sort_nodup _ _)
    rw [List.toFinset_card_of_nodup hnd, List.length_take, Nat.min_eq_left htake_le]
  have hC'sub : C ∪ pad ⊆ B := Finset.union_subset hCB (hpad_sub.trans Finset.sdiff_subset)
  have hC'card : (C ∪ pad).card = B.card / 2 := by
    rw [Finset.card_union_of_disjoint hdisj, hpad_card]
    omega
  have hsd' : (B \ (C ∪ pad)).card = (C ∪ pad).card := by
    rw [Finset.card_sdiff_of_subset hC'sub, hC'card]
    obtain ⟨m, hm⟩ := heven
    omega
  exact ⟨Finset.subset_union_left, hC'sub, hC'card, hsd'⟩

end MinCostFlow.ExpanderDecomp
