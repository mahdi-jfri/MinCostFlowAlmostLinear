module

public import MinCostFlow.Statement.Cited.Graphs
public import MinCostFlow.ExpanderDecomp.Embedding
public import MinCostFlow.ExpanderDecomp.Rounds
import MinCostFlow.Expander.GraphHelpers
import MinCostFlow.ExpanderDecomp.Injection
import Mathlib.Data.Finset.Sort
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Bisection padding, matching completion, and round-embedding accumulation

This file provides the matching-level primitives for the outer cut-matching game:

* **Bisection padding (`padToBisection`)**: given a balanced cut `U` of `V = Finset.range (2 * e)`,
  selects the smaller side `C` (`|C| ≤ e`, `4 |C| ≥ 2e`) and pads `C` to an exact bisection `(A, B)`
  of `V` with `|A| = |B| = e`, `C ⊆ A`, and `Disjoint C B`.
* **Fake-edge matching completion (`fakeCompletion`)**: given disjoint `A, B ⊆ V` with `|A| ≤ |B|`
  and a partial matching `M ⊆ A × B`, pairs the unmatched vertices of `A` and `B` in sorted order
  using `|A| - |M|` fake edges of maximum degree at most `1`, producing an injection matching
  `M ++ fakeCompletion A B M` covering `A` (and a perfect matching on `V` when `|A| = |B|` and
  `A ∪ B = V`).
* **Round-embedding accumulation (`GameEmbInv`)**: inductively maintains an embedding of the
  accumulated witness graph `W` into `Hhat + F` across `k` routing rounds, bounding host-edge
  congestion by `k * R` and fake-edge congestion by `1`.
-/

@[expose] public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited

/-- A partial matching from `A` to `B`: every edge goes from `A` to `B`, with distinct left
endpoints and distinct right endpoints. -/
def IsPartialMatching (A B : Finset ℕ) (M : List (ℕ × ℕ)) : Prop :=
  (∀ e ∈ M, e.1 ∈ A ∧ e.2 ∈ B) ∧
    (M.map Prod.fst).Nodup ∧
    (M.map Prod.snd).Nodup

/-- Select the smaller side of `U` in `Finset.range (2 * e)`. -/
def outerSmallerSide (e : ℕ) (U : Finset ℕ) : Finset ℕ :=
  if U.card ≤ (Finset.range (2 * e) \ U).card then U else Finset.range (2 * e) \ U

/-- Pad the smaller side `C = outerSmallerSide e U` to a set `A ⊆ Finset.range (2 * e)` of exact size
`e`, returning `(A, Finset.range (2 * e) \ A)`. -/
def padToBisection (e : ℕ) (U : Finset ℕ) : Finset ℕ × Finset ℕ :=
  let V := Finset.range (2 * e)
  let C := outerSmallerSide e U
  let pad := ((V \ C).sort (· ≤ ·)).take (e - C.card)
  let A := C ∪ pad.toFinset
  (A, V \ A)

/-- Complete a partial matching `M` from `A` to `B` by zipping the sorted unmatched vertices of `A`
with the sorted unmatched vertices of `B`. -/
def fakeCompletion (A B : Finset ℕ) (M : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  let unA := (A \ (M.map Prod.fst).toFinset).sort (· ≤ ·)
  let unB := (B \ (M.map Prod.snd).toFinset).sort (· ≤ ·)
  unA.zip unB

/-- Accumulated embedding invariant after `k` routing rounds into host `Hhat` with congestion
parameter `R` per round: there exists an embedding of `⟨Hhat.n, W⟩` into `⟨Hhat.n, Hhat.edges ++ F⟩`
on `Hhat.verts` with congestion at most `k * R` on host edges and at most `1` on fake edges. -/
def GameEmbInv (Hhat : Graph) (W F : List (ℕ × ℕ)) (R k : ℕ) : Prop :=
  ∃ emb : ℕ → List ℕ,
    IsEmbeddingOn ⟨Hhat.n, W⟩ ⟨Hhat.n, Hhat.edges ++ F⟩ Hhat.verts emb ∧
    (∀ i < Hhat.m, congestion ⟨Hhat.n, W⟩ emb i ≤ k * R) ∧
    (∀ i, Hhat.m ≤ i → i < Hhat.m + F.length → congestion ⟨Hhat.n, W⟩ emb i ≤ 1) ∧
    (∀ j < W.length, ∀ i ∈ emb j, i < Hhat.m + F.length)

end MinCostFlow.ExpanderDecomp

public section

namespace MinCostFlow.ExpanderDecomp

open MinCostFlow.Cited MinCostFlow.Expander

/-! ### Bisection padding -/

/-- Specification of `padToBisection e U`: when `U ⊆ V = Finset.range (2 * e)` satisfies
`2 * e ≤ 4 * |U|` and `2 * e ≤ 4 * |V \ U|`, `(A, B) = padToBisection e U` is a bisection of `V`
with `C = outerSmallerSide e U ⊆ A`, `Disjoint C B`, `2 * e ≤ 4 * |C|`, and `W.cutIn V C = W.cutIn V U`
for every graph `W`. -/
theorem padToBisection_spec {e : ℕ} {U : Finset ℕ}
    (hU : U ⊆ Finset.range (2 * e))
    (hU1 : 2 * e ≤ 4 * U.card)
    (hU2 : 2 * e ≤ 4 * (Finset.range (2 * e) \ U).card) :
    let V := Finset.range (2 * e)
    let C := outerSmallerSide e U
    let (A, B) := padToBisection e U
    C ⊆ V ∧
      2 * e ≤ 4 * C.card ∧
      C.card ≤ e ∧
      A ⊆ V ∧ B ⊆ V ∧ Disjoint A B ∧ A ∪ B = V ∧
      A.card = e ∧ B.card = e ∧
      C ⊆ A ∧ Disjoint C B ∧
      ∀ W : Graph, W.cutIn V C = W.cutIn V U := by
  set V := Finset.range (2 * e)
  set C := outerSmallerSide e U
  have hVcard : V.card = 2 * e := Finset.card_range (2 * e)
  have hUsum : (V \ U).card + U.card = 2 * e := by
    rw [Finset.card_sdiff_add_card_eq_card hU, hVcard]
  have hCV : C ⊆ V := by
    unfold C outerSmallerSide
    split_ifs
    · exact hU
    · exact Finset.sdiff_subset
  have hC4 : 2 * e ≤ 4 * C.card := by
    unfold C outerSmallerSide
    split_ifs
    · exact hU1
    · exact hU2
  have hCle : C.card ≤ e := by
    unfold C outerSmallerSide
    split_ifs with h
    · change U.card ≤ (V \ U).card at h
      omega
    · change ¬ U.card ≤ (V \ U).card at h
      change (V \ U).card ≤ e
      omega
  have hCcut : ∀ W : Graph, W.cutIn V C = W.cutIn V U := by
    intro W
    unfold C outerSmallerSide
    split_ifs
    · rfl
    · exact cutIn_sdiff W V U hU
  set pad := ((V \ C).sort (· ≤ ·)).take (e - C.card)
  set A := C ∪ pad.toFinset
  set B := V \ A
  have hsort_len : ((V \ C).sort (· ≤ ·)).length = (V \ C).card := Finset.length_sort (· ≤ ·)
  have hVC_card : (V \ C).card = 2 * e - C.card := by
    have h := Finset.card_sdiff_add_card_eq_card hCV
    omega
  have hpad_sub : pad.toFinset ⊆ V \ C := by
    intro x hx
    rw [List.mem_toFinset] at hx
    exact (Finset.mem_sort (· ≤ ·)).mp (List.mem_of_mem_take hx)
  have hpad_nd : pad.Nodup := (Finset.sort_nodup (V \ C) (· ≤ ·)).take
  have hpad_len : pad.length = e - C.card := by
    rw [List.length_take, hsort_len, hVC_card]
    omega
  have hpad_card : pad.toFinset.card = e - C.card := by
    rw [List.toFinset_card_of_nodup hpad_nd, hpad_len]
  have hdisj_Cpad : Disjoint C pad.toFinset :=
    Finset.disjoint_of_subset_right hpad_sub disjoint_sdiff_self_right
  have hAV : A ⊆ V :=
    Finset.union_subset hCV (hpad_sub.trans Finset.sdiff_subset)
  have hBV : B ⊆ V := Finset.sdiff_subset
  have hdisjAB : Disjoint A B := disjoint_sdiff_self_right
  have hunionAB : A ∪ B = V := Finset.union_sdiff_of_subset hAV
  have hAcard : A.card = e := by
    rw [Finset.card_union_of_disjoint hdisj_Cpad, hpad_card]
    omega
  have hBcard : B.card = e := by
    have h := Finset.card_sdiff_add_card_eq_card hAV
    change B.card + A.card = V.card at h
    omega
  have hCA : C ⊆ A := Finset.subset_union_left
  have hdisjCB : Disjoint C B := Finset.disjoint_of_subset_left hCA hdisjAB
  exact ⟨hCV, hC4, hCle, hAV, hBV, hdisjAB, hunionAB, hAcard, hBcard, hCA, hdisjCB, hCcut⟩

/-! ### Matching completion with fake edges -/

private theorem nodup_flatMap_pair_of_partial {A B : Finset ℕ} {M : List (ℕ × ℕ)}
    (hdisj : Disjoint A B) (hM : IsPartialMatching A B M) :
    (M.flatMap fun e => [e.1, e.2]).Nodup := by
  obtain ⟨hmem, hfst, hsnd⟩ := hM
  induction M with
  | nil => simp
  | cons e rest ih =>
    simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
      List.mem_cons, List.mem_flatMap, not_or]
    have he := hmem e List.mem_cons_self
    have hrest : IsPartialMatching A B rest :=
      ⟨fun f hf => hmem f (List.mem_cons_of_mem _ hf),
        (List.nodup_cons.mp hfst).2, (List.nodup_cons.mp hsnd).2⟩
    have hne : e.1 ≠ e.2 := fun h =>
      Finset.disjoint_left.mp hdisj he.1 (h ▸ he.2)
    have h1not : ∀ f ∈ rest, e.1 ≠ f.1 ∧ e.1 ≠ f.2 := by
      intro f hf
      refine ⟨?_, ?_⟩
      · intro heq
        exact (List.nodup_cons.mp hfst).1 (List.mem_map.mpr ⟨f, hf, heq.symm⟩)
      · intro heq
        exact Finset.disjoint_left.mp hdisj he.1 (heq ▸ (hmem f (List.mem_cons_of_mem _ hf)).2)
    have h2not : ∀ f ∈ rest, e.2 ≠ f.1 ∧ e.2 ≠ f.2 := by
      intro f hf
      refine ⟨?_, ?_⟩
      · intro heq
        exact Finset.disjoint_left.mp hdisj (heq ▸ (hmem f (List.mem_cons_of_mem _ hf)).1) he.2
      · intro heq
        exact (List.nodup_cons.mp hsnd).1 (List.mem_map.mpr ⟨f, hf, heq.symm⟩)
    refine ⟨⟨hne, ?_⟩, ?_, ih hrest.1 hrest.2.1 hrest.2.2⟩
    · rintro ⟨f, hf, hmemf⟩
      simp only [List.not_mem_nil, or_false] at hmemf
      rcases hmemf with h | h
      · exact (h1not f hf).1 h
      · exact (h1not f hf).2 h
    · rintro ⟨f, hf, hmemf⟩
      simp only [List.not_mem_nil, or_false] at hmemf
      rcases hmemf with h | h
      · exact (h2not f hf).1 h
      · exact (h2not f hf).2 h

/-- A graph whose flattened endpoint list is `Nodup` has maximum degree at most `1`. -/
theorem deg_le_one_of_nodup_flatMap {n : ℕ} {E : List (ℕ × ℕ)}
    (hnd : (E.flatMap fun e => [e.1, e.2]).Nodup) (v : ℕ) :
    (Graph.mk n E).deg v ≤ 1 := by
  have hle_all : (E.map fun e => (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)).sum ≤ 1 := by
    induction E with
    | nil => simp
    | cons e rest ih =>
      simp only [List.flatMap_cons, List.cons_append, List.nil_append, List.nodup_cons,
        List.mem_cons, List.mem_flatMap, not_or] at hnd
      simp only [List.map_cons, List.sum_cons]
      have hrest := ih hnd.2.2
      by_cases h1 : e.1 = v
      · subst h1
        have h2 : e.2 ≠ e.1 := Ne.symm hnd.1.1
        have hzero : (rest.map fun f => (if f.1 = e.1 then 1 else 0) + (if f.2 = e.1 then 1 else 0)).sum = 0 := by
          apply List.sum_eq_zero
          intro x hx
          rw [List.mem_map] at hx
          obtain ⟨f, hf, rfl⟩ := hx
          have hf1 : f.1 ≠ e.1 := fun h => hnd.1.2 ⟨f, hf, by simp [h]⟩
          have hf2 : f.2 ≠ e.1 := fun h => hnd.1.2 ⟨f, hf, by simp [h]⟩
          simp [hf1, hf2]
        simp [h2, hzero]
      · by_cases h2 : e.2 = v
        · subst h2
          have hzero : (rest.map fun f => (if f.1 = e.2 then 1 else 0) + (if f.2 = e.2 then 1 else 0)).sum = 0 := by
            apply List.sum_eq_zero
            intro x hx
            rw [List.mem_map] at hx
            obtain ⟨f, hf, rfl⟩ := hx
            have hf1 : f.1 ≠ e.2 := fun h => hnd.2.1 ⟨f, hf, by simp [h]⟩
            have hf2 : f.2 ≠ e.2 := fun h => hnd.2.1 ⟨f, hf, by simp [h]⟩
            simp [hf1, hf2]
          simp [h1, hzero]
        · simp only [h1, h2, ↓reduceIte, add_zero, zero_add]
          exact hrest
  unfold Graph.deg
  rw [degIn_eq_sum_map]
  have hsub : ((Graph.mk n E).inside (Graph.mk n E).verts).Sublist E := List.filter_sublist
  have hsum_le : (((Graph.mk n E).inside (Graph.mk n E).verts).map
      fun e => (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)).sum ≤
      (E.map fun e => (if e.1 = v then 1 else 0) + (if e.2 = v then 1 else 0)).sum :=
    List.Sublist.sum_le_sum (hsub.map _) (fun _ _ => Nat.zero_le _)
  omega

/-- Specification of `fakeCompletion A B M` for disjoint `A, B` with `|A| ≤ |B|` and a partial
matching `M` from `A` to `B`:
1. `|fakeCompletion A B M| = |A| - |M|`;
2. `fakeCompletion A B M` is a partial matching from `A` to `B` with degree `≤ 1` everywhere;
3. `M ++ fakeCompletion A B M` is a partial matching from `A` to `B` covering all of `A` with
   distinct endpoints everywhere;
4. when `A.card = B.card` and `A ∪ B = V`, `M ++ fakeCompletion A B M` is a perfect matching on `V`. -/
theorem fakeCompletion_spec {A B : Finset ℕ} {M : List (ℕ × ℕ)}
    (hdisj : Disjoint A B) (hAB : A.card ≤ B.card) (hM : IsPartialMatching A B M) :
    let F := fakeCompletion A B M
    let E := M ++ F
    F.length = A.card - M.length ∧
      IsPartialMatching A B F ∧
      (∀ n v, (Graph.mk n F).deg v ≤ 1) ∧
      IsPartialMatching A B E ∧
      (E.flatMap fun e => [e.1, e.2]).Nodup ∧
      (∀ v ∈ A, ∃ e ∈ E, e.1 = v) ∧
      (∀ V : Finset ℕ, A.card = B.card → A ∪ B = V → IsPerfectMatchingOn V E) := by
  obtain ⟨hMmem, hMfst, hMsnd⟩ := hM
  set unA := (A \ (M.map Prod.fst).toFinset).sort (· ≤ ·)
  set unB := (B \ (M.map Prod.snd).toFinset).sort (· ≤ ·)
  set F := unA.zip unB
  have hMfst_sub : (M.map Prod.fst).toFinset ⊆ A := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact (hMmem e he).1
  have hMsnd_sub : (M.map Prod.snd).toFinset ⊆ B := by
    intro x hx
    rw [List.mem_toFinset, List.mem_map] at hx
    obtain ⟨e, he, rfl⟩ := hx
    exact (hMmem e he).2
  have hMfst_card : (M.map Prod.fst).toFinset.card = M.length := by
    rw [List.toFinset_card_of_nodup hMfst, List.length_map]
  have hMsnd_card : (M.map Prod.snd).toFinset.card = M.length := by
    rw [List.toFinset_card_of_nodup hMsnd, List.length_map]
  have hunA_len : unA.length = A.card - M.length := by
    rw [Finset.length_sort, Finset.card_sdiff_of_subset hMfst_sub, hMfst_card]
  have hunB_len : unB.length = B.card - M.length := by
    rw [Finset.length_sort, Finset.card_sdiff_of_subset hMsnd_sub, hMsnd_card]
  have hlen_le : unA.length ≤ unB.length := by omega
  have hF_len : F.length = A.card - M.length := by
    rw [List.length_zip, min_eq_left hlen_le, hunA_len]
  have hF_fst : F.map Prod.fst = unA := List.map_fst_zip hlen_le
  have hF_snd_sub : (F.map Prod.snd).Sublist unB := by
    have htake : ∀ (l₁ l₂ : List ℕ), (l₁.zip l₂).map Prod.snd = l₂.take l₁.length := by
      intro l₁
      induction l₁ with
      | nil => intro l₂; simp
      | cons a t₁ ih =>
        intro l₂
        cases l₂ with
        | nil => simp
        | cons b t₂ => simp [ih]
    rw [show F = unA.zip unB from rfl, htake]
    exact List.take_sublist _ _
  have hF_mem : ∀ e ∈ F, e.1 ∈ A ∧ e.2 ∈ B := by
    intro e he
    have h1 : e.1 ∈ unA := List.of_mem_zip he |>.1
    have h2 : e.2 ∈ unB := List.of_mem_zip he |>.2
    rw [Finset.mem_sort] at h1 h2
    exact ⟨(Finset.mem_sdiff.mp h1).1, (Finset.mem_sdiff.mp h2).1⟩
  have hF_fst_nd : (F.map Prod.fst).Nodup := by
    rw [hF_fst]
    exact Finset.sort_nodup _ _
  have hF_snd_nd : (F.map Prod.snd).Nodup :=
    (Finset.sort_nodup _ _).sublist hF_snd_sub
  have hF_pm : IsPartialMatching A B F := ⟨hF_mem, hF_fst_nd, hF_snd_nd⟩
  have hF_deg : ∀ n v, (Graph.mk n F).deg v ≤ 1 := fun n v =>
    deg_le_one_of_nodup_flatMap (nodup_flatMap_pair_of_partial hdisj hF_pm) v
  have hE_fst_nd : ((M ++ F).map Prod.fst).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨hMfst, hF_fst_nd, ?_⟩
    intro x hxM y hyF hxy
    subst hxy
    rw [hF_fst, Finset.mem_sort, Finset.mem_sdiff] at hyF
    exact hyF.2 (List.mem_toFinset.mpr hxM)
  have hE_snd_nd : ((M ++ F).map Prod.snd).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨hMsnd, hF_snd_nd, ?_⟩
    intro x hxM y hyF hxy
    subst hxy
    have hyB : x ∈ unB := hF_snd_sub.subset hyF
    rw [Finset.mem_sort, Finset.mem_sdiff] at hyB
    exact hyB.2 (List.mem_toFinset.mpr hxM)
  have hE_mem : ∀ e ∈ M ++ F, e.1 ∈ A ∧ e.2 ∈ B := by
    intro e he
    rcases List.mem_append.mp he with h | h
    · exact hMmem e h
    · exact hF_mem e h
  have hE_pm : IsPartialMatching A B (M ++ F) := ⟨hE_mem, hE_fst_nd, hE_snd_nd⟩
  have hE_nd : ((M ++ F).flatMap fun e => [e.1, e.2]).Nodup :=
    nodup_flatMap_pair_of_partial hdisj hE_pm
  have hE_covA : ∀ v ∈ A, ∃ e ∈ M ++ F, e.1 = v := by
    intro v hvA
    by_cases hvM : v ∈ (M.map Prod.fst).toFinset
    · rw [List.mem_toFinset, List.mem_map] at hvM
      obtain ⟨e, he, rfl⟩ := hvM
      exact ⟨e, List.mem_append_left F he, rfl⟩
    · have hvunA : v ∈ unA := (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_sdiff.mpr ⟨hvA, hvM⟩)
      rw [← hF_fst, List.mem_map] at hvunA
      obtain ⟨e, he, rfl⟩ := hvunA
      exact ⟨e, List.mem_append_right M he, rfl⟩
  have hE_perf : ∀ V : Finset ℕ, A.card = B.card → A ∪ B = V → IsPerfectMatchingOn V (M ++ F) := by
    intro V hcard hunion
    have hun_eq : unA.length = unB.length := by omega
    have hF_snd : F.map Prod.snd = unB := List.map_snd_zip (le_of_eq hun_eq.symm)
    refine ⟨?_, hE_nd, ?_⟩
    · intro e he
      have hm := hE_mem e he
      rw [← hunion]
      exact ⟨Finset.mem_union_left B hm.1, Finset.mem_union_right A hm.2⟩
    · intro u huV
      rw [← hunion, Finset.mem_union] at huV
      rcases huV with huA | huB
      · obtain ⟨e, he, h1⟩ := hE_covA u huA
        exact ⟨e, he, Or.inl h1⟩
      · by_cases huM : u ∈ (M.map Prod.snd).toFinset
        · rw [List.mem_toFinset, List.mem_map] at huM
          obtain ⟨e, he, rfl⟩ := huM
          exact ⟨e, List.mem_append_left F he, Or.inr rfl⟩
        · have huunB : u ∈ unB := (Finset.mem_sort (· ≤ ·)).mpr (Finset.mem_sdiff.mpr ⟨huB, huM⟩)
          rw [← hF_snd, List.mem_map] at huunB
          obtain ⟨e, he, rfl⟩ := huunB
          exact ⟨e, List.mem_append_right M he, Or.inr rfl⟩
  exact ⟨hF_len, hF_pm, hF_deg, hE_pm, hE_nd, hE_covA, hE_perf⟩

/-! ### Round-embedding accumulation -/

private theorem edgeAt_append_left {E₁ E₂ : List (ℕ × ℕ)} {j : ℕ} (hj : j < E₁.length) :
    edgeAt (E₁ ++ E₂) j = edgeAt E₁ j := by
  unfold edgeAt
  rw [List.getD_append _ _ _ _ hj]

private theorem edgeAt_append_right {E₁ E₂ : List (ℕ × ℕ)} {j : ℕ} (hj : E₁.length ≤ j) :
    edgeAt (E₁ ++ E₂) j = edgeAt E₂ (j - E₁.length) := by
  unfold edgeAt
  by_cases hlt : j < (E₁ ++ E₂).length
  · have hlt2 : j - E₁.length < E₂.length := by simp only [List.length_append] at hlt; omega
    rw [List.getD_eq_getElem _ _ hlt, List.getD_eq_getElem _ _ hlt2,
      List.getElem_append_right hj]
  · have hge2 : E₂.length ≤ j - E₁.length := by simp only [List.length_append] at hlt; omega
    simp only [List.getD, List.getElem?_eq_none (not_lt.mp hlt), List.getElem?_eq_none hge2,
      Option.getD_none]

private theorem isEdgeWalk_append_right {E₁ E₂ : List (ℕ × ℕ)} {u v : ℕ} {es : List ℕ}
    (h : IsEdgeWalk E₁ u v es) : IsEdgeWalk (E₁ ++ E₂) u v es := by
  induction h with
  | nil u => exact IsEdgeWalk.nil u
  | cons hj hend _ ih =>
    refine IsEdgeWalk.cons (by simp only [List.length_append]; omega) ?_ ih
    rwa [edgeAt_append_left hj]

/-- Initial empty embedding invariant at round `0`. -/
theorem GameEmbInv.empty (Hhat : Graph) (R : ℕ) : GameEmbInv Hhat [] [] R 0 := by
  refine ⟨fun _ => [], ?_, ?_, ?_, ?_⟩
  · intro j hj
    exact absurd hj (Nat.not_lt_zero j)
  · intro i _
    simp [congestion]
  · intro i hi1 hi2
    simp only [List.length_nil, add_zero] at hi2
    omega
  · intro j hj
    exact absurd hj (Nat.not_lt_zero j)

/-- Appending one routing round `(M_real, M_fake)` advances `GameEmbInv` from `k` to `k + 1`. -/
theorem GameEmbInv.append_round {Hhat : Graph} {W F M_real M_fake : List (ℕ × ℕ)} {R k : ℕ}
    (hacc : GameEmbInv Hhat W F R k)
    {emb_r : ℕ → List ℕ}
    (hemb_r : IsEmbeddingOn ⟨Hhat.n, M_real⟩ Hhat Hhat.verts emb_r)
    (hcong_r : ∀ i < Hhat.m, congestion ⟨Hhat.n, M_real⟩ emb_r i ≤ R)
    (hM_real_ends : ∀ e ∈ M_real, e.1 ∈ Hhat.verts ∧ e.2 ∈ Hhat.verts)
    (hM_fake_ends : ∀ e ∈ M_fake, e.1 ∈ Hhat.verts ∧ e.2 ∈ Hhat.verts) :
    GameEmbInv Hhat (W ++ (M_real ++ M_fake)) (F ++ M_fake) R (k + 1) := by
  obtain ⟨emb, hemb, hcong_h, hcong_f, hlt_emb⟩ := hacc
  set m₀ := Hhat.m
  set w₀ := W.length
  set r₀ := M_real.length
  set f₀ := F.length
  set emb' : ℕ → List ℕ := fun j =>
    if j < w₀ then emb j
    else if j < w₀ + r₀ then emb_r (j - w₀)
    else [m₀ + f₀ + (j - w₀ - r₀)]
  have hKeq : Hhat.edges ++ (F ++ M_fake) = (Hhat.edges ++ F) ++ M_fake :=
    (List.append_assoc _ _ _).symm
  have hinside_all : ∀ {L : List (ℕ × ℕ)} {j : ℕ},
      (∀ e ∈ L, e.1 ∈ Hhat.verts ∧ e.2 ∈ Hhat.verts) → j < L.length →
      insideB Hhat.verts (edgeAt L j) = true := by
    intro L j hL hj
    have hmem : edgeAt L j ∈ L := by
      unfold edgeAt
      rw [List.getD_eq_getElem _ _ hj]
      exact List.getElem_mem hj
    have h := hL _ hmem
    simp [insideB, h.1, h.2]
  refine ⟨emb', ?_, ?_, ?_, ?_⟩
  · -- IsEmbeddingOn
    intro j hj hin
    change j < (W ++ (M_real ++ M_fake)).length at hj
    by_cases hj1 : j < w₀
    · have hed : edgeAt (W ++ (M_real ++ M_fake)) j = edgeAt W j := edgeAt_append_left hj1
      rw [hed] at hin ⊢
      have he := hemb j hj1 hin
      have hemb'_eq : emb' j = emb j := by simp [emb', hj1]
      rw [hemb'_eq]
      refine ⟨?_, ?_⟩
      · rw [hKeq]
        exact isEdgeWalk_append_right he.1
      · intro i hi
        have hilt : i < (Hhat.edges ++ F).length := he.1.lt_length i hi
        rw [hKeq, edgeAt_append_left hilt]
        exact he.2 i hi
    · by_cases hj2 : j < w₀ + r₀
      · have hjr : j - w₀ < r₀ := by omega
        have hed : edgeAt (W ++ (M_real ++ M_fake)) j = edgeAt M_real (j - w₀) := by
          rw [edgeAt_append_right (by omega), edgeAt_append_left hjr]
        rw [hed] at hin ⊢
        have he := hemb_r (j - w₀) hjr hin
        have hemb'_eq : emb' j = emb_r (j - w₀) := by simp [emb', hj1, hj2]
        rw [hemb'_eq]
        refine ⟨isEdgeWalk_append_right he.1, ?_⟩
        intro i hi
        have hilt : i < Hhat.edges.length := he.1.lt_length i hi
        rw [edgeAt_append_left hilt]
        exact he.2 i hi
      · have hjf : j - w₀ - r₀ < M_fake.length := by
          simp only [List.length_append] at hj; omega
        have hed : edgeAt (W ++ (M_real ++ M_fake)) j = edgeAt M_fake (j - w₀ - r₀) := by
          rw [edgeAt_append_right (by omega), edgeAt_append_right (by omega)]
        have hemb'_eq : emb' j = [m₀ + f₀ + (j - w₀ - r₀)] := by simp [emb', hj1, hj2]
        rw [hed, hemb'_eq]
        set idx := m₀ + f₀ + (j - w₀ - r₀)
        have hidx_lt : idx < (Hhat.edges ++ (F ++ M_fake)).length := by
          simp only [List.length_append, idx, m₀, f₀, Graph.m]; omega
        have hidx_ed : edgeAt (Hhat.edges ++ (F ++ M_fake)) idx = edgeAt M_fake (j - w₀ - r₀) := by
          rw [hKeq, edgeAt_append_right (by simp only [List.length_append, idx, m₀, f₀, Graph.m]; omega)]
          have hsub : idx - (Hhat.edges ++ F).length = j - w₀ - r₀ := by
            simp only [List.length_append, idx, m₀, f₀, Graph.m]; omega
          rw [hsub]
        refine ⟨IsEdgeWalk.cons hidx_lt (Or.inl ⟨by rw [hidx_ed], by rw [hidx_ed]⟩) (IsEdgeWalk.nil _), ?_⟩
        intro i hi
        simp only [List.mem_singleton] at hi
        subst hi
        rw [hidx_ed]
        exact hinside_all hM_fake_ends hjf
  · -- Congestion on real host edges `i < m₀`
    intro i hi
    unfold congestion
    change ((Finset.range (W ++ (M_real ++ M_fake)).length).filter fun j => i ∈ emb' j).card ≤
      (k + 1) * R
    set S := (Finset.range (W ++ (M_real ++ M_fake)).length).filter fun j => i ∈ emb' j
    set S₁ := (Finset.range w₀).filter fun j => i ∈ emb j
    set S₂ := (Finset.range r₀).filter fun j => i ∈ emb_r j
    have hsub : S ⊆ S₁ ∪ S₂.image (fun j => w₀ + j) := by
      intro j hj
      simp only [S, Finset.mem_filter, Finset.mem_range] at hj
      by_cases hj1 : j < w₀
      · simp only [emb', hj1, ↓reduceIte] at hj
        exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, hj.2⟩)
      · by_cases hj2 : j < w₀ + r₀
        · simp only [emb', hj1, hj2, ↓reduceIte] at hj
          apply Finset.mem_union_right
          rw [Finset.mem_image]
          refine ⟨j - w₀, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hj.2⟩, by omega⟩
        · simp only [emb', hj1, hj2, ↓reduceIte, List.mem_singleton] at hj
          omega
    have hcard := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
    have himg : (S₂.image fun j => w₀ + j).card ≤ S₂.card := Finset.card_image_le
    have h1 : S₁.card ≤ k * R := hcong_h i hi
    have h2 : S₂.card ≤ R := hcong_r i hi
    have hring : (k + 1) * R = k * R + R := by ring
    omega
  · -- Congestion on fake edges `m₀ ≤ i < m₀ + (F ++ M_fake).length`
    intro i hi1 hi2
    unfold congestion
    change ((Finset.range (W ++ (M_real ++ M_fake)).length).filter fun j => i ∈ emb' j).card ≤ 1
    set S := (Finset.range (W ++ (M_real ++ M_fake)).length).filter fun j => i ∈ emb' j
    by_cases hif : i < m₀ + f₀
    · have hsub : S ⊆ (Finset.range w₀).filter fun j => i ∈ emb j := by
        intro j hj
        simp only [S, Finset.mem_filter, Finset.mem_range] at hj
        by_cases hj1 : j < w₀
        · simp only [emb', hj1, ↓reduceIte] at hj
          exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj1, hj.2⟩
        · by_cases hj2 : j < w₀ + r₀
          · simp only [emb', hj1, hj2, ↓reduceIte] at hj
            have hlt_r : j - w₀ < M_real.length := by omega
            have hin := hinside_all hM_real_ends hlt_r
            have hilt := (hemb_r (j - w₀) hlt_r hin).1.lt_length i hj.2
            change i < m₀ at hilt
            omega
          · simp only [emb', hj1, hj2, ↓reduceIte, List.mem_singleton] at hj
            omega
      exact le_trans (Finset.card_le_card hsub) (hcong_f i hi1 hif)
    · have hsub : S ⊆ {w₀ + r₀ + (i - (m₀ + f₀))} := by
        intro j hj
        simp only [S, Finset.mem_filter, Finset.mem_range] at hj
        rw [Finset.mem_singleton]
        by_cases hj1 : j < w₀
        · simp only [emb', hj1, ↓reduceIte] at hj
          have hilt := hlt_emb j hj1 i hj.2
          omega
        · by_cases hj2 : j < w₀ + r₀
          · simp only [emb', hj1, hj2, ↓reduceIte] at hj
            have hlt_r : j - w₀ < M_real.length := by omega
            have hin := hinside_all hM_real_ends hlt_r
            have hilt := (hemb_r (j - w₀) hlt_r hin).1.lt_length i hj.2
            change i < m₀ at hilt
            omega
          · simp only [emb', hj1, hj2, ↓reduceIte, List.mem_singleton] at hj
            omega
      exact le_trans (Finset.card_le_card hsub) (by simp)
  · -- Edge index bound
    intro j hj i hi
    simp only [List.length_append] at hj ⊢
    by_cases hj1 : j < w₀
    · simp only [emb', hj1, ↓reduceIte] at hi
      have := hlt_emb j hj1 i hi
      omega
    · by_cases hj2 : j < w₀ + r₀
      · simp only [emb', hj1, hj2, ↓reduceIte] at hi
        have hlt_r : j - w₀ < M_real.length := by omega
        have hin := hinside_all hM_real_ends hlt_r
        have hilt := (hemb_r (j - w₀) hlt_r hin).1.lt_length i hi
        change i < m₀ at hilt
        omega
      · simp only [emb', hj1, hj2, ↓reduceIte, List.mem_singleton] at hi
        omega

/-- Extract a uniform congestion bound `max (k * R) 1` (hence `≤ k * R` when `1 ≤ k * R`) on all
edges of `Hhat + F` from `GameEmbInv`. -/
theorem GameEmbInv.congestion_le {Hhat : Graph} {W F : List (ℕ × ℕ)} {R k η : ℕ}
    (hacc : GameEmbInv Hhat W F R k) (h1 : 1 ≤ η) (hkR : k * R ≤ η) :
    ∃ emb : ℕ → List ℕ,
      IsEmbeddingOn ⟨Hhat.n, W⟩ ⟨Hhat.n, Hhat.edges ++ F⟩ Hhat.verts emb ∧
      ∀ i < (Graph.mk Hhat.n (Hhat.edges ++ F)).m, congestion ⟨Hhat.n, W⟩ emb i ≤ η := by
  obtain ⟨emb, hemb, hch, hcf, _⟩ := hacc
  refine ⟨emb, hemb, fun i hi => ?_⟩
  change i < (Hhat.edges ++ F).length at hi
  rw [List.length_append] at hi
  by_cases hlt : i < Hhat.m
  · exact le_trans (hch i hlt) hkR
  · exact le_trans (hcf i (by omega) hi) h1

/-- Degree adds over appended edge lists. -/
theorem deg_append (n : ℕ) (E₁ E₂ : List (ℕ × ℕ)) (v : ℕ) :
    (Graph.mk n (E₁ ++ E₂)).deg v = (Graph.mk n E₁).deg v + (Graph.mk n E₂).deg v := by
  unfold Graph.deg
  rw [degIn_eq_sum_map, degIn_eq_sum_map, degIn_eq_sum_map]
  unfold Graph.inside Graph.verts
  dsimp only
  rw [List.filter_append, List.map_append, List.sum_append]

end MinCostFlow.ExpanderDecomp
