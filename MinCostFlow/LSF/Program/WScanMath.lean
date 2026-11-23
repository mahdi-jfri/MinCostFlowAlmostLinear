module

public import Mathlib.Data.List.Basic
public import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Tactic

/-!
# The groups of a sorted list

The `W` block lists the pieces of `refineDecomp`. The program finds them by sorting the kept
indices by key and then scanning the sorted list. A new group starts at each position whose key
differs from the key before it. Each group keeps its elements and a list of vertices without
repeats: each element `x` adds `x` and `pa x` when they are not yet in the list of its group.

`wGroups K s pa k` is the list of groups after the first `k` positions `s 0, …, s (k - 1)`. Each
group is a pair: its elements, and its vertices. This file proves the facts about it that the
bridge to the `W` block uses (`wGroups_spec`).
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

/-- Adds `y` at the end of `l` when it is not in `l`. -/
def addNew (l : List ℕ) (y : ℕ) : List ℕ := if y ∈ l then l else l ++ [y]

/-- Adds the element `x` to a group: `x` to the elements, `x` and `pa x` to the vertices. -/
def grpAdd (pa : ℕ → ℕ) (p : List ℕ × List ℕ) (x : ℕ) : List ℕ × List ℕ :=
  (p.1 ++ [x], addNew (addNew p.2 x) (pa x))

/-- Applies `f` to the last group (an empty group when there is none). -/
def pushLast (f : List ℕ × List ℕ → List ℕ × List ℕ) (G : List (List ℕ × List ℕ)) :
    List (List ℕ × List ℕ) :=
  G.dropLast ++ [f (G.getLastD ([], []))]

/-- Position `k` starts a new group. -/
def IsBoundary (K s : ℕ → ℕ) (k : ℕ) : Prop := k = 0 ∨ K (s (k - 1)) ≠ K (s k)

instance (K s : ℕ → ℕ) (k : ℕ) : Decidable (IsBoundary K s k) := by
  unfold IsBoundary; infer_instance

/-- The groups after the first `k` positions. -/
def wGroups (K s pa : ℕ → ℕ) : ℕ → List (List ℕ × List ℕ)
  | 0 => []
  | k + 1 =>
    pushLast (fun p => grpAdd pa p (s k))
      (if IsBoundary K s k then wGroups K s pa k ++ [([], [])] else wGroups K s pa k)

lemma addNew_nodup {l : List ℕ} (h : l.Nodup) (y : ℕ) : (addNew l y).Nodup := by
  unfold addNew
  split_ifs with hy
  · exact h
  · exact List.nodup_append.mpr ⟨h, List.nodup_singleton y, by
      intro a ha b hb hab; rw [List.mem_singleton.mp hb] at hab; exact hy (hab ▸ ha)⟩

lemma mem_addNew {l : List ℕ} {y z : ℕ} : z ∈ addNew l y ↔ z ∈ l ∨ z = y := by
  unfold addNew
  split_ifs with hy
  · constructor
    · exact Or.inl
    · rintro (h | rfl)
      · exact h
      · exact hy
  · simp

lemma addNew_length_le (l : List ℕ) (y : ℕ) : (addNew l y).length ≤ l.length + 1 := by
  unfold addNew; split_ifs <;> simp

lemma headD_mem' {l : List ℕ} (h : l ≠ []) : l.headD 0 ∈ l := by
  cases l with
  | nil => exact absurd rfl h
  | cons a l => exact List.mem_cons_self

lemma pushLast_append (f : List ℕ × List ℕ → List ℕ × List ℕ) (G : List (List ℕ × List ℕ))
    (p : List ℕ × List ℕ) : pushLast f (G ++ [p]) = G ++ [f p] := by
  simp [pushLast]

lemma pushLast_of_ne_nil (f : List ℕ × List ℕ → List ℕ × List ℕ) {G : List (List ℕ × List ℕ)}
    (hG : G ≠ []) : pushLast f G = G.dropLast ++ [f (G.getLast hG)] := by
  simp [pushLast, List.getLastD_eq_getLast?, List.getLast?_eq_some_getLast hG]

lemma dropLast_append_getLast' {G : List (List ℕ × List ℕ)} (hG : G ≠ []) :
    G = G.dropLast ++ [G.getLast hG] := (List.dropLast_append_getLast hG).symm

/-- One step of `wGroups`, in the form `G' ++ [last]`. -/
lemma wGroups_succ (K s pa : ℕ → ℕ) (k : ℕ) :
    wGroups K s pa (k + 1) =
      if IsBoundary K s k then wGroups K s pa k ++ [grpAdd pa ([], []) (s k)]
      else pushLast (fun p => grpAdd pa p (s k)) (wGroups K s pa k) := by
  rw [wGroups]
  split_ifs
  · exact pushLast_append _ _ _
  · rfl

/-- The facts about the groups after `k` positions, when the keys of the first `m ≥ k`
positions do not decrease. -/
structure GroupsInv (K s pa : ℕ → ℕ) (k : ℕ) (G : List (List ℕ × List ℕ)) : Prop where
  hflat : (G.map Prod.fst).flatten = (List.range k).map s
  hne : ∀ p ∈ G, p.1 ≠ []
  hkey : ∀ p ∈ G, ∀ x ∈ p.1, K x = K (p.1.headD 0)
  hlt : G.Pairwise (fun p q => K (p.1.headD 0) < K (q.1.headD 0))
  hvert : ∀ p ∈ G, p.2.Nodup ∧ ∀ y, y ∈ p.2 ↔ ∃ x ∈ p.1, y = x ∨ y = pa x
  hvlen : ∀ p ∈ G, p.2.length ≤ 2 * p.1.length
  hlast : ∀ hG : G ≠ [], 0 < k → s (k - 1) ∈ (G.getLast hG).1
  hnil : G = [] ↔ k = 0

lemma groupsInv_zero (K s pa : ℕ → ℕ) : GroupsInv K s pa 0 [] where
  hflat := by simp
  hne := by simp
  hkey := by simp
  hlt := List.Pairwise.nil
  hvert := by simp
  hvlen := by simp
  hlast := fun h => absurd rfl h
  hnil := by simp

lemma grpAdd_vert (pa : ℕ → ℕ) {p : List ℕ × List ℕ}
    (hp : p.2.Nodup ∧ ∀ y, y ∈ p.2 ↔ ∃ x ∈ p.1, y = x ∨ y = pa x) (x : ℕ) :
    (grpAdd pa p x).2.Nodup ∧
      ∀ y, y ∈ (grpAdd pa p x).2 ↔ ∃ z ∈ (grpAdd pa p x).1, y = z ∨ y = pa z := by
  refine ⟨addNew_nodup (addNew_nodup hp.1 x) (pa x), fun y => ?_⟩
  simp only [grpAdd, mem_addNew, hp.2, List.mem_append, List.mem_singleton]
  constructor
  · rintro ((⟨z, hz, hyz⟩ | rfl) | rfl)
    · exact ⟨z, Or.inl hz, hyz⟩
    · exact ⟨y, Or.inr rfl, Or.inl rfl⟩
    · exact ⟨x, Or.inr rfl, Or.inr rfl⟩
  · rintro ⟨z, hz | rfl, hyz | hyz⟩
    · exact Or.inl (Or.inl ⟨z, hz, Or.inl hyz⟩)
    · exact Or.inl (Or.inl ⟨z, hz, Or.inr hyz⟩)
    · exact Or.inl (Or.inr hyz)
    · exact Or.inr hyz

lemma grpAdd_vlen (pa : ℕ → ℕ) {p : List ℕ × List ℕ} (hp : p.2.length ≤ 2 * p.1.length)
    (x : ℕ) : (grpAdd pa p x).2.length ≤ 2 * (grpAdd pa p x).1.length := by
  have h1 := addNew_length_le p.2 x
  have h2 := addNew_length_le (addNew p.2 x) (pa x)
  simp only [grpAdd, List.length_append, List.length_singleton]
  omega

/-- The step of `GroupsInv`. -/
lemma GroupsInv.succ {K s pa : ℕ → ℕ} {k m : ℕ} (hkm : k < m)
    (hsort : ∀ i j, i ≤ j → j < m → K (s i) ≤ K (s j))
    {G : List (List ℕ × List ℕ)} (hG : GroupsInv K s pa k G) (hGk : G = wGroups K s pa k) :
    GroupsInv K s pa (k + 1) (wGroups K s pa (k + 1)) := by
  rw [wGroups_succ, ← hGk]
  have hrange : (List.range (k + 1)).map s = (List.range k).map s ++ [s k] := by
    rw [List.range_succ, List.map_append]; rfl
  -- every earlier element has key at most that of position `k - 1`
  have hprev : ∀ p ∈ G, ∀ x ∈ p.1, ∃ j < k, x = s j := by
    intro p hp x hx
    have : x ∈ (G.map Prod.fst).flatten := List.mem_flatten.mpr ⟨p.1, List.mem_map_of_mem hp, hx⟩
    rw [hG.hflat] at this
    obtain ⟨j, hj, rfl⟩ := List.mem_map.mp this
    exact ⟨j, List.mem_range.mp hj, rfl⟩
  split_ifs with hb
  · -- a new group
    have hlt_new : ∀ p ∈ G, K (p.1.headD 0) < K (s k) := by
      intro p hp
      obtain ⟨j, hj, hjx⟩ := hprev p hp _ (headD_mem' (hG.hne p hp))
      rw [hjx]
      have hk0 : k ≠ 0 := by
        rintro rfl; exact absurd hj (Nat.not_lt_zero _)
      have hne : K (s (k - 1)) ≠ K (s k) := hb.resolve_left hk0
      have h1 := hsort j (k - 1) (by omega) (by omega)
      have h2 := hsort (k - 1) k (by omega) hkm
      omega
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simp [hG.hflat, hrange, grpAdd]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hG.hne p hp
      · rw [List.mem_singleton.mp hp]; simp [grpAdd]
    · intro p hp x hx
      rcases List.mem_append.mp hp with hp | hp
      · exact hG.hkey p hp x hx
      · rw [List.mem_singleton.mp hp] at hx ⊢; simp_all [grpAdd]
    · refine List.pairwise_append.mpr ⟨hG.hlt, List.pairwise_singleton _ _, ?_⟩
      intro p hp q hq
      rw [List.mem_singleton.mp hq]
      simpa [grpAdd] using hlt_new p hp
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hG.hvert p hp
      · rw [List.mem_singleton.mp hp]
        exact grpAdd_vert pa (p := ([], [])) (by simp) _
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hG.hvlen p hp
      · rw [List.mem_singleton.mp hp]
        exact grpAdd_vlen pa (p := ([], [])) (by simp) _
    · intro _ _
      simp [grpAdd]
    · simp
  · -- the last group grows
    have hk0 : k ≠ 0 := fun h => hb (Or.inl h)
    have hGne : G ≠ [] := fun h => hk0 (hG.hnil.mp h)
    have hsame : K (s (k - 1)) = K (s k) := by
      by_contra hc; exact hb (Or.inr hc)
    rw [pushLast_of_ne_nil _ hGne]
    set q := G.getLast hGne with hq
    have hqG : q ∈ G := List.getLast_mem hGne
    have hGsplit : G = G.dropLast ++ [q] := dropLast_append_getLast' hGne
    have hdrop : ∀ p ∈ G.dropLast, p ∈ G := fun p hp => List.mem_of_mem_dropLast hp
    have hqne := hG.hne q hqG
    have hqhead : (q.1 ++ [s k]).headD 0 = q.1.headD 0 := by
      cases h : q.1 with
      | nil => exact absurd h hqne
      | cons a l => rfl
    have hqkey : K (s k) = K (q.1.headD 0) := by
      rw [← hsame]; exact hG.hkey q hqG _ (hG.hlast hGne (by omega))
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have h := hG.hflat
      rw [hGsplit] at h
      simp only [List.map_append, List.map_singleton, List.flatten_append,
        List.flatten_singleton] at h ⊢
      rw [hrange, ← h]
      simp [grpAdd]
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hG.hne p (hdrop p hp)
      · rw [List.mem_singleton.mp hp]; simp [grpAdd]
    · intro p hp x hx
      rcases List.mem_append.mp hp with hp | hp
      · exact hG.hkey p (hdrop p hp) x hx
      · rw [List.mem_singleton.mp hp] at hx ⊢
        simp only [grpAdd] at hx ⊢
        rw [hqhead]
        rcases List.mem_append.mp hx with hx | hx
        · exact hG.hkey q hqG x hx
        · rw [List.mem_singleton.mp hx]; exact hqkey
    · have h := hG.hlt
      rw [hGsplit] at h
      obtain ⟨h1, -, h3⟩ := List.pairwise_append.mp h
      refine List.pairwise_append.mpr ⟨h1, List.pairwise_singleton _ _, ?_⟩
      intro p hp q' hq'
      rw [List.mem_singleton.mp hq']
      simp only [grpAdd, hqhead]
      exact h3 p hp q (List.mem_singleton_self q)
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hG.hvert p (hdrop p hp)
      · rw [List.mem_singleton.mp hp]
        exact grpAdd_vert pa (hG.hvert q hqG) _
    · intro p hp
      rcases List.mem_append.mp hp with hp | hp
      · exact hG.hvlen p (hdrop p hp)
      · rw [List.mem_singleton.mp hp]
        exact grpAdd_vlen pa (hG.hvlen q hqG) _
    · intro _ _
      simp [grpAdd]
    · simp

/-- The invariant holds for every `k ≤ m`. -/
theorem groupsInv_of_le {K s pa : ℕ → ℕ} {m : ℕ}
    (hsort : ∀ i j, i ≤ j → j < m → K (s i) ≤ K (s j)) :
    ∀ k ≤ m, GroupsInv K s pa k (wGroups K s pa k)
  | 0, _ => groupsInv_zero K s pa
  | k + 1, hk => (groupsInv_of_le hsort k (by omega)).succ (by omega) hsort rfl

/-! ## Lengths and offsets -/

/-- The number of elements in the first `i` groups. -/
def eStart (G : List (List ℕ × List ℕ)) (i : ℕ) : ℕ := ((G.take i).map (·.1.length)).sum

/-- The number of vertices in the first `i` groups. -/
def vStart (G : List (List ℕ × List ℕ)) (i : ℕ) : ℕ := ((G.take i).map (·.2.length)).sum

lemma eStart_length {K s pa : ℕ → ℕ} {k : ℕ} {G : List (List ℕ × List ℕ)}
    (hG : GroupsInv K s pa k G) : eStart G G.length = k := by
  have h := congrArg List.length hG.hflat
  simp only [List.length_flatten, List.map_map, List.length_map, List.length_range] at h
  simpa [eStart, Function.comp_def] using h

/-- The total number of vertices. -/
def vTotal (G : List (List ℕ × List ℕ)) : ℕ := vStart G G.length

lemma vStart_le_vTotal (G : List (List ℕ × List ℕ)) {i : ℕ} :
    vStart G i ≤ vTotal G := by
  simp only [vTotal, vStart, List.take_length]
  rw [List.map_take]
  conv_rhs => rw [← List.take_append_drop i (G.map (·.2.length))]
  rw [List.sum_append]
  omega

lemma vTotal_le {K s pa : ℕ → ℕ} {k : ℕ} {G : List (List ℕ × List ℕ)}
    (hG : GroupsInv K s pa k G) : vTotal G ≤ 2 * k := by
  have h := eStart_length hG
  unfold vTotal vStart
  unfold eStart at h
  rw [List.take_length] at h ⊢
  rw [← h, ← List.sum_map_mul_left]
  refine List.sum_le_sum fun p hp => ?_
  simpa using hG.hvlen p hp

lemma length_le {K s pa : ℕ → ℕ} {k : ℕ} {G : List (List ℕ × List ℕ)}
    (hG : GroupsInv K s pa k G) : G.length ≤ k := by
  have h := eStart_length hG
  unfold eStart at h
  rw [List.take_length] at h
  rw [← h]
  have : ∀ p ∈ G, 1 ≤ p.1.length := fun p hp => List.length_pos_iff.mpr (hG.hne p hp)
  calc G.length = (G.map (fun _ => 1)).sum := by simp
    _ ≤ _ := List.sum_le_sum fun p hp => this p hp

lemma start_succ (f : List ℕ × List ℕ → ℕ) (G : List (List ℕ × List ℕ)) {i : ℕ}
    (hi : i < G.length) : ((G.take (i + 1)).map f).sum = ((G.take i).map f).sum + f G[i] := by
  rw [List.take_add_one, List.getElem?_eq_getElem hi]
  simp only [Option.toList, List.map_append, List.sum_append, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, add_zero]

/-- The entries of a flattened list from the start of block `i`. -/
lemma getElem_flatten_start (L : List (List ℕ)) {i t : ℕ} (hi : i < L.length)
    (ht : t < L[i].length) :
    ∃ h : ((L.take i).map List.length).sum + t < L.flatten.length,
      L.flatten[((L.take i).map List.length).sum + t] = L[i][t] := by
  have hsplit : L.flatten = (L.take i).flatten ++ (L[i] ++ (L.drop (i + 1)).flatten) := by
    conv_lhs => rw [← List.take_append_drop i L, List.drop_eq_getElem_cons hi]
    rw [List.flatten_append, List.flatten_cons]
  have hlen : (L.take i).flatten.length = ((L.take i).map List.length).sum :=
    List.length_flatten
  have hb : ((L.take i).map List.length).sum + t < L.flatten.length := by
    rw [hsplit]; simp only [List.length_append]; omega
  refine ⟨hb, ?_⟩
  simp only [hsplit]
  rw [List.getElem_append_right (by omega), List.getElem_append_left (by omega)]
  congr 1
  omega

end MinCostFlow.LSF.Program

end
