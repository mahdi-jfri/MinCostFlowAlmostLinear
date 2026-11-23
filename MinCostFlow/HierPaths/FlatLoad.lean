module

public import MinCostFlow.HierPaths.FlatWalk
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# The occurrence load of the flattened connectors (composition)

This file bounds how often an edge of the root host occurs in all flattened connector walks of
one depth. A *family* at depth `t` is a list of walks, each tagged with the group at depth `t`
whose host it lives in. Lifting a family one depth up (`liftFam`) replaces each walk by its
substitution into the host of the parent group. The load of a family on edge `i` of the host of
group `a` (`groupLoad`) counts the occurrences of `i` in the walks tagged `a`.

The key step (`groupLoad_liftFam_le`): if every host edge at depth `t + 1` has load at most `r`,
then every host edge of a group `a` at depth `t` has load at most `r · ρ t` after lifting. The
reason: an occurrence of `i` in a lifted walk comes from an occurrence of an edge `e` of a child
host `c` of `a` together with an occurrence of `i` in the embedding walk of `e`, and the
embeddings of all children of `a` together put load at most `ρ t` on `i` (`HierData.Bounds`).
The children of different groups live in different hosts, so they do not add up.

Iterating (`occLoad_flatFam_le`) gives load `r · ∏_{k < t} ρ k` on the root host. For the
connectors of depth `t` (`connFam`), the start load is at most `B² · κ t` with `B = 2 ^ b`: each
group has fewer than `B²` pairs of children, each with load at most `κ t`
(`groupLoad_connFam_le`). So only the last family contributes the factor `B²`
(`occLoad_flatConnFam_le`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The load of the family `F` (entries `(group, start, walk)`) on edge `i` of the host of
group `a`. -/
def groupLoad (F : List (ℕ × ℕ × List ℕ)) (a i : ℕ) : ℕ :=
  ((F.filter fun p => p.1 = a).map fun p => p.2.2.count i).sum

/-- Lift a family at depth `t + 1` to depth `t`: substitute each walk into the host of the parent
group. -/
def liftFam (H : HierData) (x b t : ℕ) (F : List (ℕ × ℕ × List ℕ)) : List (ℕ × ℕ × List ℕ) :=
  F.map fun p => (parentGroup x b t p.1, p.2.1,
    substWalk (H.host (t + 1) p.1).edges (H.emb t p.1) p.2.1 p.2.2)

/-- Flatten a family at depth `t` to the root host, keeping the start vertices. -/
def flatFam (H : HierData) (x b t : ℕ) (F : List (ℕ × ℕ × List ℕ)) : List (ℕ × List ℕ) :=
  F.map fun p => (p.2.1, flatWalk H x b t p.1 p.2.1 p.2.2)

/-- The family at depth `t` is well formed: each walk is tagged with a group at depth `t` and uses
only edges of its host. -/
def FamOK (H : HierData) (x b t : ℕ) (F : List (ℕ × ℕ × List ℕ)) : Prop :=
  ∀ p ∈ F, p.1 < numGroups x b t ∧ ∀ e ∈ p.2.2, e < (H.host t p.1).m

/-- The children of group `g` at depth `t`, as a list. -/
def childList (x b t g : ℕ) : List ℕ := List.range' (g * branching x b t) (branching x b t)

/-- The connectors of the children `c < c'` of group `g` at depth `t`, as a family at depth `t`. -/
def pairFam (H : HierData) (t g c c' : ℕ) : List (ℕ × ℕ × List ℕ) :=
  if c < c' then (H.conn t c c').map fun q => (g, q.1, q.2.2) else []

/-- All connectors of depth `t`, as a family at depth `t`. -/
def connFam (H : HierData) (x b t : ℕ) : List (ℕ × ℕ × List ℕ) :=
  (List.range (numGroups x b t)).flatMap fun g =>
    (childList x b t g).flatMap fun c => (childList x b t g).flatMap fun c' => pairFam H t g c c'

/-- All connectors of all depths above the leaves, flattened to the root host. -/
def flatConnFam (H : HierData) (x b : ℕ) : List (ℕ × List ℕ) :=
  (List.range (leafDepth x b)).flatMap fun t => flatFam H x b t (connFam H x b t)

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open MinCostFlow.Cited MinCostFlow.ExpanderDecomp HierData

variable {x b : ℕ} {H : HierData}

theorem groupLoad_nil (a i : ℕ) : groupLoad [] a i = 0 := rfl

theorem groupLoad_cons (p : ℕ × ℕ × List ℕ) (F : List (ℕ × ℕ × List ℕ)) (a i : ℕ) :
    groupLoad (p :: F) a i = (if p.1 = a then p.2.2.count i else 0) + groupLoad F a i := by
  unfold groupLoad
  rw [List.filter_cons]
  by_cases h : p.1 = a
  · simp [h]
  · simp [h]

theorem groupLoad_append (F F' : List (ℕ × ℕ × List ℕ)) (a i : ℕ) :
    groupLoad (F ++ F') a i = groupLoad F a i + groupLoad F' a i := by
  unfold groupLoad
  rw [List.filter_append, List.map_append, List.sum_append]

theorem groupLoad_flatMap {α : Type*} (l : List α) (f : α → List (ℕ × ℕ × List ℕ)) (a i : ℕ) :
    groupLoad (l.flatMap f) a i = (l.map fun g => groupLoad (f g) a i).sum := by
  induction l with
  | nil => rfl
  | cons g l ih => rw [List.flatMap_cons, groupLoad_append, ih, List.map_cons, List.sum_cons]

/-- A family all of whose walks are tagged `g ≠ a` has no load on the hosts of `a`. -/
theorem groupLoad_eq_zero_of_tag {F : List (ℕ × ℕ × List ℕ)} {g a : ℕ} (hF : ∀ p ∈ F, p.1 = g)
    (hga : g ≠ a) (i : ℕ) : groupLoad F a i = 0 := by
  induction F with
  | nil => rfl
  | cons p F ih =>
    rw [groupLoad_cons, ih fun q hq => hF q (List.mem_cons_of_mem _ hq),
      hF p List.mem_cons_self]
    simp [hga]

/-- A sum over a list of terms that are each at most `K` is at most `K` times its length. -/
theorem sum_map_le_length_mul' {α : Type*} {l : List α} {f : α → ℕ} {K : ℕ}
    (h : ∀ a ∈ l, f a ≤ K) : (l.map f).sum ≤ l.length * K := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, List.length_cons, Nat.succ_mul]
    have h1 := h a List.mem_cons_self
    have h2 := ih fun j hj => h j (List.mem_cons_of_mem _ hj)
    omega

theorem flatFam_zero (F : List (ℕ × ℕ × List ℕ)) :
    flatFam H x b 0 F = F.map fun p => (p.2.1, p.2.2) := by
  simp [flatFam, flatWalk]

theorem flatFam_succ (t : ℕ) (F : List (ℕ × ℕ × List ℕ)) :
    flatFam H x b (t + 1) F = flatFam H x b t (liftFam H x b t F) := by
  simp [flatFam, liftFam, flatWalk]

theorem famOK_liftFam (hH : H.IsValid x b) {t : ℕ} (hs : 1 < groupSize x b (t + 1))
    {F : List (ℕ × ℕ × List ℕ)} (hF : FamOK H x b (t + 1) F) :
    FamOK H x b t (liftFam H x b t F) := by
  intro p hp
  simp only [liftFam, List.mem_map] at hp
  obtain ⟨q, hq, rfl⟩ := hp
  obtain ⟨hq1, hq2⟩ := hF q hq
  refine ⟨parentGroup_lt_numGroups hq1, fun e he => ?_⟩
  obtain ⟨j, hj, hej⟩ := mem_substWalk he
  exact (hH.emb_walk hs hq1 (hq2 j hj)).lt_length e hej

/-- The load of a lifted family regroups over the children `c` of `a` and the edges `e` of their
hosts. -/
theorem groupLoad_liftFam (t : ℕ) {F : List (ℕ × ℕ × List ℕ)} (hF : FamOK H x b (t + 1) F)
    (a i : ℕ) :
    groupLoad (liftFam H x b t F) a i =
      ∑ c ∈ childGroups x b t a, ∑ e ∈ Finset.range (H.host (t + 1) c).m,
        groupLoad F c e * (H.emb t c e).count i := by
  induction F with
  | nil => simp [liftFam, groupLoad_nil]
  | cons p F ih =>
    have ih' := ih fun q hq => hF q (List.mem_cons_of_mem _ hq)
    have hp := hF p List.mem_cons_self
    simp only [liftFam, List.map_cons] at ih' ⊢
    rw [groupLoad_cons, ih']
    simp only [groupLoad_cons, Nat.add_mul, Finset.sum_add_distrib]
    congr 1
    have hinner : ∀ c, ∑ e ∈ Finset.range (H.host (t + 1) c).m,
        (if p.1 = c then p.2.2.count e else 0) * (H.emb t c e).count i =
          if p.1 = c then ∑ e ∈ Finset.range (H.host (t + 1) p.1).m,
            p.2.2.count e * (H.emb t p.1 e).count i else 0 := by
      intro c
      split_ifs with h
      · subst h; rfl
      · simp
    rw [Finset.sum_congr rfl fun c _ => hinner c, Finset.sum_ite_eq, count_substWalk,
      sum_map_eq_sum_range_count hp.2]
    simp only [mem_childGroups_iff]

/-- **One lifting step of the load.** If every host edge at depth `t + 1` has load at most `r`,
every host edge of a group `a` at depth `t` has load at most `r · ρ t` after lifting. -/
theorem groupLoad_liftFam_le {d ρ κ : ℕ → ℕ} (hB : H.Bounds x b d ρ κ) {t : ℕ}
    (hs : 1 < groupSize x b (t + 1)) {F : List (ℕ × ℕ × List ℕ)} (hF : FamOK H x b (t + 1) F)
    {r : ℕ} (hr : ∀ c < numGroups x b (t + 1), ∀ e < (H.host (t + 1) c).m, groupLoad F c e ≤ r)
    {a : ℕ} (ha : a < numGroups x b t) {i : ℕ} (hi : i < (H.host t a).m) :
    groupLoad (liftFam H x b t F) a i ≤ r * ρ t := by
  rw [groupLoad_liftFam t hF]
  have hc : ∀ c ∈ childGroups x b t a, c < numGroups x b (t + 1) := by
    intro c hc
    have hm : c * groupSize x b (t + 1) ∈ members x b t a := by
      rw [members_eq_biUnion_childGroups]
      refine Finset.mem_biUnion.mpr ⟨c, hc, ?_⟩
      simp only [members, Finset.mem_Ico, Nat.succ_mul]
      exact ⟨le_rfl, Nat.lt_add_of_pos_right groupSize_pos⟩
    have hlt := Finset.mem_range.mp (members_subset_range ha hm)
    have hg : groupOf x b (t + 1) (c * groupSize x b (t + 1)) = c := by
      unfold groupOf
      exact Nat.mul_div_cancel _ groupSize_pos
    rw [← hg]
    exact groupOf_lt_numGroups hlt
  calc ∑ c ∈ childGroups x b t a, ∑ e ∈ Finset.range (H.host (t + 1) c).m,
        groupLoad F c e * (H.emb t c e).count i
      ≤ ∑ c ∈ childGroups x b t a, ∑ e ∈ Finset.range (H.host (t + 1) c).m,
        r * (H.emb t c e).count i :=
        Finset.sum_le_sum fun c hc' => Finset.sum_le_sum fun e he =>
          Nat.mul_le_mul_right _ (hr c (hc c hc') e (Finset.mem_range.mp he))
    _ = r * ∑ c ∈ childGroups x b t a, ∑ e ∈ Finset.range (H.host (t + 1) c).m,
        (H.emb t c e).count i := by
        simp only [Finset.mul_sum]
    _ ≤ r * ρ t := Nat.mul_le_mul_left _ (hB.emb_load t a hs ha i hi)

/-- **The load of a flattened family.** If every host edge at depth `t` has load at most `r` in
the family `F`, every edge of the root host occurs at most `r · ∏_{k < t} ρ k` times in the
flattened family. -/
theorem occLoad_flatFam_le (hH : H.IsValid x b) {d ρ κ : ℕ → ℕ} (hB : H.Bounds x b d ρ κ) :
    ∀ {t : ℕ}, 1 < groupSize x b t → ∀ {F : List (ℕ × ℕ × List ℕ)}, FamOK H x b t F →
      ∀ {r : ℕ}, (∀ a < numGroups x b t, ∀ i < (H.host t a).m, groupLoad F a i ≤ r) →
        ∀ i, occLoad (flatFam H x b t F) i ≤ r * ∏ k ∈ Finset.range t, ρ k
  | 0, _, F, hF, r, hr, i => by
    have h0 : ∀ p ∈ F, p.1 = 0 := by
      intro p hp
      have := (hF p hp).1
      simp only [numGroups, Nat.zero_mul, Nat.min_zero, pow_zero] at this
      omega
    have heq : occLoad (flatFam H x b 0 F) i = groupLoad F 0 i := by
      rw [flatFam_zero]
      unfold occLoad groupLoad
      rw [List.filter_eq_self.mpr (fun p hp => by simp [h0 p hp]), List.map_map]
      rfl
    rw [heq, Finset.prod_range_zero, Nat.mul_one]
    by_cases hi : i < (H.host 0 0).m
    · exact hr 0 (by simp [numGroups]) i hi
    · have hz : groupLoad F 0 i = 0 := by
        unfold groupLoad
        refine List.sum_eq_zero fun n hn => ?_
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hn
        have hp' := (List.mem_filter.mp hp).1
        refine List.count_eq_zero.mpr fun hmem => hi ?_
        have := (hF p hp').2 i hmem
        rwa [h0 p hp'] at this
      omega
  | t + 1, hs, F, hF, r, hr, i => by
    rw [flatFam_succ, Finset.prod_range_succ, Nat.mul_comm _ (ρ t), ← Nat.mul_assoc]
    exact occLoad_flatFam_le hH hB (hs.trans_le (groupSize_succ_le t)) (famOK_liftFam hH hs hF)
      (fun a ha i hi => groupLoad_liftFam_le hB hs hF hr ha hi) i

theorem mem_childList {t g c : ℕ} : c ∈ childList x b t g ↔ c ∈ childGroups x b t g := by
  simp only [childList, List.mem_range'_1, childGroups, Finset.mem_Ico, Nat.succ_mul]

theorem length_childList (t g : ℕ) : (childList x b t g).length = branching x b t :=
  List.length_range'

theorem famOK_connFam (hH : H.IsValid x b) {t : ℕ} (hs : 1 < groupSize x b t) :
    FamOK H x b t (connFam H x b t) := by
  intro p hp
  simp only [connFam, List.mem_flatMap, List.mem_range] at hp
  obtain ⟨g, hg, c, hc, c', hc', hp⟩ := hp
  unfold pairFam at hp
  split_ifs at hp with hcc
  · obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    exact ⟨hg, (hH.conn_walk t g hs hg c (mem_childList.mp hc) c' (mem_childList.mp hc') hcc q
      hq).lt_length⟩
  · simp at hp

/-- **The start load of the connectors.** On each host edge of a group at depth `t`, the
connectors of its pairs of children have load at most `r² · κ t`, for `r` children. -/
theorem groupLoad_connFam_le {d ρ κ : ℕ → ℕ} (hB : H.Bounds x b d ρ κ) {t : ℕ}
    (hs : 1 < groupSize x b t) {a : ℕ} (ha : a < numGroups x b t) {i : ℕ}
    (hi : i < (H.host t a).m) :
    groupLoad (connFam H x b t) a i ≤ branching x b t * branching x b t * κ t := by
  have htag : ∀ g, ∀ p ∈ ((childList x b t g).flatMap fun c =>
      (childList x b t g).flatMap fun c' => pairFam H t g c c'), p.1 = g := by
    intro g p hp
    simp only [List.mem_flatMap] at hp
    obtain ⟨c, _, c', _, hp⟩ := hp
    unfold pairFam at hp
    split_ifs at hp
    · obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp; rfl
    · simp at hp
  -- only the block of `a` contributes
  have hblock : groupLoad (connFam H x b t) a i = groupLoad ((childList x b t a).flatMap fun c =>
      (childList x b t a).flatMap fun c' => pairFam H t a c c') a i := by
    unfold connFam
    rw [groupLoad_flatMap]
    have hsplit := List.mem_range.mpr ha
    obtain ⟨l₁, l₂, hl⟩ := List.append_of_mem hsplit
    have hnd := List.nodup_range (n := numGroups x b t)
    rw [hl] at hnd ⊢
    have hna₁ : a ∉ l₁ := fun h => (List.nodup_append.mp hnd).2.2 a h a
      List.mem_cons_self rfl
    have hna₂ : a ∉ l₂ := (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1
    have hz : ∀ l : List ℕ, a ∉ l →
        (l.map fun g => groupLoad ((childList x b t g).flatMap fun c =>
          (childList x b t g).flatMap fun c' => pairFam H t g c c') a i).sum = 0 := by
      intro l hl'
      refine List.sum_eq_zero fun n hn => ?_
      obtain ⟨g, hg, rfl⟩ := List.mem_map.mp hn
      exact groupLoad_eq_zero_of_tag (htag g) (fun he => hl' (by rw [← he]; exact hg)) i
    rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons, hz l₁ hna₁,
      hz l₂ hna₂, Nat.zero_add, Nat.add_zero]
  rw [hblock, groupLoad_flatMap]
  refine (sum_map_le_length_mul' (K := branching x b t * κ t) fun c hc => ?_).trans ?_
  · rw [groupLoad_flatMap]
    refine (sum_map_le_length_mul' (K := κ t) fun c' hc' => ?_).trans ?_
    · unfold pairFam
      split_ifs with hcc
      · unfold groupLoad
        rw [List.filter_eq_self.mpr (fun p hp => by
          obtain ⟨q, _, rfl⟩ := List.mem_map.mp hp; simp), List.map_map]
        exact hB.conn_load t a hs ha c (mem_childList.mp hc) c' (mem_childList.mp hc') hcc i hi
      · exact Nat.zero_le _
    · rw [length_childList]
  · rw [length_childList, Nat.mul_assoc]

end MinCostFlow.HierPaths
