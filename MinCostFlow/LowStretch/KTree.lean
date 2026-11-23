module

public import MinCostFlow.LowStretch.Walks

/-!
# Kruskal trees

The program merges the vertices along the pairs in the order of their weights, as Kruskal's
algorithm does, and keeps the merge tree. A node of this tree is a set of vertices (the leaves
below it) with the weight of the pair that merged it. This file states what the program must
build (`KT.Ok`) and proves the facts that the clusters need:
* the nodes of weight below `x` that are maximal (the *`x`-nodes*, `KT.IsTop`) are the classes of
  the vertices joined by pairs lighter than `x` (`KT.top_of_walk`, `KT.walk_of_under`);
* inside a node of weight `μ` every two vertices are joined by pairs of weight at most `μ` that
  stay inside the node (`KT.walk_of_under`).

Nodes `0, …, n - 1` are the vertices. Every other node is made by a merge, after its two children,
so a parent has a larger number than its children. The last node is the root.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- A merge tree on the vertices `0, …, n - 1`. -/
structure KT where
  /-- The number of nodes. -/
  N : ℕ
  /-- The parent (the root is its own parent). -/
  par : ℕ → ℕ
  /-- The first child. -/
  ch1 : ℕ → ℕ
  /-- The second child. -/
  ch2 : ℕ → ℕ
  /-- The merge weight (`0` for a vertex). -/
  mw : ℕ → ℕ
  /-- The pair that made the merge. -/
  mp : ℕ → ℕ

namespace KT

variable (T : KT)

/-- `j` is below `k` (or equal). -/
def Under (j k : ℕ) : Prop := ∃ i, T.par^[i] j = k

/-- `p` goes between the two children of `k`. -/
def Splits (G : PG) (p k : ℕ) : Prop :=
  T.Under (G.pu p) (T.ch1 k) ∧ T.Under (G.pv p) (T.ch2 k) ∨
    T.Under (G.pu p) (T.ch2 k) ∧ T.Under (G.pv p) (T.ch1 k)

/-- The rules for a merge tree of the pair graph `G`. -/
structure Ok (G : PG) : Prop where
  n_lt : G.n < T.N
  par_lt : ∀ k, k + 1 < T.N → k < T.par k ∧ T.par k < T.N
  root : T.par (T.N - 1) = T.N - 1
  leaf_mw : ∀ v < G.n, T.mw v = 0
  mw_mono : ∀ k < T.N, T.mw k ≤ T.mw (T.par k)
  par_internal : ∀ k, k + 1 < T.N → G.n ≤ T.par k
  par_ch : ∀ k, k + 1 < T.N → k = T.ch1 (T.par k) ∨ k = T.ch2 (T.par k)
  ch : ∀ k, G.n ≤ k → k < T.N → T.par (T.ch1 k) = k ∧ T.par (T.ch2 k) = k ∧
    T.ch1 k ≠ T.ch2 k ∧ T.ch1 k < k ∧ T.ch2 k < k
  merge : ∀ k, G.n ≤ k → k < T.N → T.mp k < G.m ∧ G.pω (T.mp k) = T.mw k ∧ T.Splits G (T.mp k) k
  lca : ∀ p < G.m, ∀ k, G.n ≤ k → k < T.N → T.Splits G p k → T.mw k ≤ G.pω p
  all : ∀ v < G.n, T.Under v (T.N - 1)

variable {T} {G : PG}

theorem Under.refl (j : ℕ) : T.Under j j := ⟨0, rfl⟩

theorem Under.trans {a b c : ℕ} (h1 : T.Under a b) (h2 : T.Under b c) : T.Under a c := by
  obtain ⟨i, rfl⟩ := h1
  obtain ⟨i', rfl⟩ := h2
  exact ⟨i' + i, by rw [Function.iterate_add_apply]⟩

theorem Under.par (j : ℕ) : T.Under j (T.par j) := ⟨1, rfl⟩

/-- The nodes above a node form a chain. -/
theorem Under.total {v j k : ℕ} (h1 : T.Under v j) (h2 : T.Under v k) : T.Under j k ∨ T.Under k j := by
  obtain ⟨i, rfl⟩ := h1
  obtain ⟨i', rfl⟩ := h2
  rcases Nat.le_total i i' with h | h
  · left
    refine ⟨i' - i, ?_⟩
    rw [← Function.iterate_add_apply]
    congr 1
    omega
  · right
    refine ⟨i - i', ?_⟩
    rw [← Function.iterate_add_apply]
    congr 1
    omega

/-- Nodes stay nodes when going up. -/
theorem par_lt_N (h : T.Ok G) {k : ℕ} (hk : k < T.N) : T.par k < T.N := by
  by_cases hr : k + 1 < T.N
  · exact (h.par_lt k hr).2
  · have : k = T.N - 1 := by omega
    rw [this, h.root]
    omega

theorem iter_lt_N (h : T.Ok G) {k : ℕ} (hk : k < T.N) (i : ℕ) : T.par^[i] k < T.N := by
  induction i with
  | zero => exact hk
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact par_lt_N h ih

theorem Under.lt_N (h : T.Ok G) {j k : ℕ} (hj : j < T.N) (hu : T.Under j k) : k < T.N := by
  obtain ⟨i, rfl⟩ := hu
  exact iter_lt_N h hj i

/-- Going up does not lower the number. -/
theorem le_par (h : T.Ok G) {k : ℕ} (hk : k < T.N) : k ≤ T.par k := by
  by_cases hr : k + 1 < T.N
  · exact (h.par_lt k hr).1.le
  · have : k = T.N - 1 := by omega
    rw [this, h.root]

theorem Under.le (h : T.Ok G) {j k : ℕ} (hj : j < T.N) (hu : T.Under j k) : j ≤ k := by
  obtain ⟨i, rfl⟩ := hu
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (le_par h (iter_lt_N h hj i))

theorem Under.mw_le (h : T.Ok G) {j k : ℕ} (hj : j < T.N) (hu : T.Under j k) : T.mw j ≤ T.mw k := by
  obtain ⟨i, rfl⟩ := hu
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    exact ih.trans (h.mw_mono _ (iter_lt_N h hj i))

/-- Below a vertex there is only the vertex. -/
theorem under_leaf (h : T.Ok G) {j v : ℕ} (hj : j < T.N) (hv : v < G.n) (hu : T.Under j v) : j = v := by
  obtain ⟨i, hi⟩ := hu
  cases i with
  | zero => exact hi
  | succ i =>
    rw [Function.iterate_succ_apply'] at hi
    have hl := iter_lt_N h hj i
    by_cases hr : T.par^[i] j + 1 < T.N
    · have := h.par_internal _ hr
      omega
    · have e : T.par^[i] j = T.N - 1 := by omega
      rw [e, h.root] at hi
      have := h.n_lt
      omega

/-- A strict step up: if `k` is below `l` and differs from it, the parent of `k` is below `l`. -/
theorem Under.par_of_ne (h : T.Ok G) {k l : ℕ} (hu : T.Under k l) (hne : k ≠ l) :
    T.Under (T.par k) l := by
  obtain ⟨i, hi⟩ := hu
  cases i with
  | zero => exact absurd hi hne
  | succ i =>
    refine ⟨i, ?_⟩
    rw [← Function.iterate_succ_apply]
    exact hi

/-! ### The lowest common node -/

/-- If `a` is below `c₁`, `b` below `c₂`, and these are the two different children of `l`, the
pair splits `l`. Every pair between two vertices of a node `l` but not of one child of `l`
splits `l`. -/
theorem splits_of (h : T.Ok G) {p l : ℕ} (hp : p < G.m) (hpu : G.pu p < G.n) (hpv : G.pv p < G.n)
    (hl : G.n ≤ l) (hlN : l < T.N) {ca cb : ℕ} (hca : ca + 1 < T.N) (hcb : cb + 1 < T.N)
    (hpa : T.par ca = l) (hpb : T.par cb = l) (hne : ca ≠ cb)
    (hua : T.Under (G.pu p) ca) (hub : T.Under (G.pv p) cb) : T.Splits G p l := by
  have h1 := h.par_ch ca hca
  have h2 := h.par_ch cb hcb
  rw [hpa] at h1
  rw [hpb] at h2
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne
  · left; rw [← h1, ← h2]; exact ⟨hua, hub⟩
  · right; rw [← h1, ← h2]; exact ⟨hua, hub⟩
  · exact absurd (h1.trans h2.symm) hne

/-- Every node reaches the root in `N` steps. -/
theorem reach_root (h : T.Ok G) {k : ℕ} (hk : k < T.N) : T.par^[T.N] k = T.N - 1 := by
  have key : ∀ i, T.par^[i] k = T.N - 1 ∨ k + i ≤ T.par^[i] k := by
    intro i
    induction i with
    | zero => right; simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with e | e
      · left; rw [e, h.root]
      · by_cases hr : T.par^[i] k + 1 < T.N
        · right; have := (h.par_lt _ hr).1; omega
        · left
          have hl := iter_lt_N h hk i
          have e' : T.par^[i] k = T.N - 1 := by omega
          rw [e', h.root]
  rcases key T.N with e | e
  · exact e
  · have := iter_lt_N h hk T.N
    omega

/-- On the way from `v` up to `l`, there is a child of `l`. -/
theorem child_on_path {v l : ℕ} (hu : T.Under v l) (hne : v ≠ l) :
    ∃ c, T.Under v c ∧ T.par c = l ∧ c ≠ l := by
  obtain ⟨i, hi⟩ := hu
  induction i with
  | zero => exact absurd hi hne
  | succ i ih =>
    rw [Function.iterate_succ_apply'] at hi
    by_cases hc : T.par^[i] v = l
    · exact ih hc
    · exact ⟨_, ⟨i, rfl⟩, hi, hc⟩

/-- **The lowest common node.** If every node split by `a` and `b` (they lie below two
different children) weighs at most `w`, some node above both weighs at most `w`. -/
theorem lca_le (h : T.Ok G) {a b w : ℕ} (ha : a < G.n) (hb : b < G.n)
    (hs : ∀ l ca cb, ca + 1 < T.N → cb + 1 < T.N → T.par ca = l → T.par cb = l → ca ≠ cb →
      T.Under a ca → T.Under b cb → T.mw l ≤ w) :
    ∃ l, T.Under a l ∧ T.Under b l ∧ T.mw l ≤ w := by
  classical
  have hN := h.n_lt
  have haN : a < T.N := by omega
  have hex : ∃ i, T.Under b (T.par^[i] a) := ⟨T.N, by rw [reach_root h haN]; exact h.all b hb⟩
  obtain ⟨i, hi, hmin⟩ : ∃ i, T.Under b (T.par^[i] a) ∧ ∀ j < i, ¬ T.Under b (T.par^[j] a) :=
    ⟨Nat.find hex, Nat.find_spec hex, fun j hj => Nat.find_min hex hj⟩
  refine ⟨T.par^[i] a, ⟨i, rfl⟩, hi, ?_⟩
  cases i with
  | zero =>
    simp only [Function.iterate_zero, id_eq]
    rw [h.leaf_mw a ha]
    exact Nat.zero_le _
  | succ j =>
    have hj := hmin j (by omega)
    rw [Function.iterate_succ_apply'] at hi ⊢
    have hcaN := iter_lt_N h haN j
    have hca1 : T.par^[j] a + 1 < T.N := by
      by_contra hc
      have e : T.par^[j] a = T.N - 1 := by omega
      rw [e, h.root, ← e] at hi
      exact hj hi
    have hln := h.par_internal _ hca1
    have hbl : b ≠ T.par (T.par^[j] a) := by omega
    obtain ⟨cb, hub, hpb, hcbl⟩ := child_on_path hi hbl
    have hcbN : cb < T.N := by
      have := Under.lt_N h (by omega) hub
      exact this
    have hcb1 : cb + 1 < T.N := by
      by_contra hc
      have e : cb = T.N - 1 := by omega
      rw [e, h.root] at hpb
      exact hcbl (e.trans hpb)
    have hne : T.par^[j] a ≠ cb := by
      intro he
      exact hj (he ▸ hub)
    exact hs _ _ _ hca1 hcb1 rfl hpb hne ⟨j, rfl⟩ hub

/-- **A pair is at least as heavy as some node above both its ends.** -/
theorem exists_lca (h : T.Ok G) {p : ℕ} (hp : p < G.m) (hpu : G.pu p < G.n) (hpv : G.pv p < G.n) :
    ∃ l, T.Under (G.pu p) l ∧ T.Under (G.pv p) l ∧ T.mw l ≤ G.pω p := by
  refine lca_le h hpu hpv fun l ca cb hca hcb hpa hpb hne hua hub => ?_
  have hlN : l < T.N := by rw [← hpa]; exact par_lt_N h (by omega)
  have hln : G.n ≤ l := by rw [← hpa]; exact h.par_internal ca hca
  exact h.lca p hp l hln hlN (splits_of h hp hpu hpv hln hlN hca hcb hpa hpb hne hua hub)

/-! ### The `x`-nodes -/

/-- `k` is the `x`-node of `v`: the highest node above `v` of weight below `x`. -/
def IsTop (x v k : ℕ) : Prop :=
  T.Under v k ∧ T.mw k < x ∧ (k + 1 < T.N → x ≤ T.mw (T.par k))

/-- A vertex has at most one `x`-node. -/
theorem IsTop.unique (h : T.Ok G) {x v k k' : ℕ} (hv : v < T.N) (h1 : T.IsTop x v k)
    (h2 : T.IsTop x v k') : k = k' := by
  rcases Under.total h1.1 h2.1 with hu | hu
  · by_contra hne
    have hkN := h1.1.lt_N h hv
    have hk1 : k + 1 < T.N := by
      have := hu.le h hkN
      have := h2.1.lt_N h hv
      omega
    have := (hu.par_of_ne h hne).mw_le h (par_lt_N h hkN)
    have := h1.2.2 hk1
    have := h2.2.1
    omega
  · by_contra hne
    have hkN := h2.1.lt_N h hv
    have hk1 : k' + 1 < T.N := by
      have := hu.le h hkN
      have := h1.1.lt_N h hv
      omega
    have := (hu.par_of_ne h (Ne.symm hne)).mw_le h (par_lt_N h hkN)
    have := h2.2.2 hk1
    have := h1.2.1
    omega

/-- If `a` and `b` lie below a node of weight below `x`, they have the same `x`-node. -/
theorem IsTop.of_common (h : T.Ok G) {x a b k l : ℕ} (haN : a < T.N) (ht : T.IsTop x a k)
    (hl1 : T.Under a l) (hl2 : T.Under b l) (hlw : T.mw l < x) : T.IsTop x b k := by
  refine ⟨?_, ht.2.1, ht.2.2⟩
  rcases Under.total hl1 ht.1 with hu | hu
  · exact hl2.trans hu
  · by_contra hn
    have hne : k ≠ l := fun he => hn (he ▸ hl2)
    have hkN := ht.1.lt_N h haN
    have hk1 : k + 1 < T.N := by
      have := hu.le h hkN
      have := hl1.lt_N h haN
      omega
    have := (hu.par_of_ne h hne).mw_le h (par_lt_N h hkN)
    have := ht.2.2 hk1
    omega

/-- **Light walks stay in an `x`-node.** -/
theorem top_of_walk (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) {V : Set ℕ}
    {x a b k : ℕ} {ps : List ℕ} (hw : G.IsWalk V {p | G.pω p < x} a b ps)
    (ht : T.IsTop x a k) : T.IsTop x b k := by
  induction hw with
  | nil => exact ht
  | @cons a b c p ps ha hp hj _ ih =>
    apply ih
    obtain ⟨hpm, he⟩ := hj
    have h1 := hG p hpm
    obtain ⟨l, hl1, hl2, hlw⟩ := exists_lca h hpm h1.1 h1.2
    have hlx : T.mw l < x := lt_of_le_of_lt hlw hp
    have hN := h.n_lt
    rcases he with ⟨e1, e2⟩ | ⟨e1, e2⟩
    · have hA : a < T.N := by rw [← e1]; omega
      rw [e1] at hl1; rw [e2] at hl2
      exact ht.of_common h hA hl1 hl2 hlx
    · have hA : a < T.N := by rw [← e2]; omega
      rw [e1] at hl1; rw [e2] at hl2
      exact ht.of_common h hA hl2 hl1 hlx

/-- The vertices below a node. -/
def leaves (G : PG) (k : ℕ) : Set ℕ := {v | v < G.n ∧ T.Under v k}

/-- **Inside a node**: two vertices below `k` are joined by a walk below `k` whose pairs weigh at
most `mw k`. -/
theorem walk_of_under (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) :
    ∀ k < T.N, ∀ a b, a < G.n → b < G.n → T.Under a k → T.Under b k →
      ∃ ps, G.IsWalk (T.leaves G k) {p | G.pω p ≤ T.mw k} a b ps := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk a b ha hb hua hub
    have hN := h.n_lt
    by_cases hkn : k < G.n
    · have e1 := under_leaf h (by omega) hkn hua
      have e2 := under_leaf h (by omega) hkn hub
      subst e1; subst e2
      exact ⟨[], .nil ⟨ha, Under.refl _⟩⟩
    push Not at hkn
    obtain ⟨hp1, hp2, hne, hlt1, hlt2⟩ := h.ch k hkn hk
    -- each vertex below `k` but not `k` itself lies below one of the children
    have hchild : ∀ v, v < G.n → T.Under v k → T.Under v (T.ch1 k) ∨ T.Under v (T.ch2 k) := by
      intro v hv hu
      obtain ⟨c, huc, hpc, hck⟩ := child_on_path hu (by omega)
      have hcN : c < T.N := Under.lt_N h (by omega) huc
      have hc1 : c + 1 < T.N := by
        by_contra hn
        have e : c = T.N - 1 := by omega
        rw [e, h.root] at hpc
        exact hck (e.trans hpc)
      rcases h.par_ch c hc1 with e | e <;> rw [hpc] at e
      · left; rw [← e]; exact huc
      · right; rw [← e]; exact huc
    -- walks inside a child are walks inside `k`
    have hsub : ∀ c, T.par c = k → T.leaves G c ⊆ T.leaves G k := fun c hc v ⟨hv, hu⟩ =>
      ⟨hv, hu.trans (by rw [← hc]; exact Under.par c)⟩
    have hmw : ∀ c, c < T.N → T.par c = k → T.mw c ≤ T.mw k := fun c hc hpc => by
      rw [← hpc]; exact h.mw_mono c hc
    have hin : ∀ c, c < k → T.par c = k → ∀ a b, a < G.n → b < G.n → T.Under a c →
        T.Under b c → ∃ ps, G.IsWalk (T.leaves G k) {p | G.pω p ≤ T.mw k} a b ps := by
      intro c hc hpc a b ha hb hua hub
      obtain ⟨ps, hps⟩ := ih c hc (by omega) a b ha hb hua hub
      exact ⟨ps, hps.mono (hsub c hpc) fun p hp => le_trans hp (hmw c (by omega) hpc)⟩
    -- the merge pair joins the two children
    obtain ⟨hmp, hmω, hsp⟩ := h.merge k hkn hk
    have hmG := hG _ hmp
    have hcross : ∃ a1 b2, a1 < G.n ∧ b2 < G.n ∧ T.Under a1 (T.ch1 k) ∧ T.Under b2 (T.ch2 k) ∧
        ∃ ps, G.IsWalk (T.leaves G k) {p | G.pω p ≤ T.mw k} a1 b2 ps := by
      rcases hsp with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · refine ⟨_, _, hmG.1, hmG.2, h1, h2, [T.mp k], .cons ⟨hmG.1, h1.trans ?_⟩ (by
          show G.pω (T.mp k) ≤ T.mw k; omega) ⟨hmp, Or.inl ⟨rfl, rfl⟩⟩ (.nil ⟨hmG.2, h2.trans ?_⟩)⟩
        · have := Under.par (T := T) (T.ch1 k); rwa [hp1] at this
        · have := Under.par (T := T) (T.ch2 k); rwa [hp2] at this
      · refine ⟨_, _, hmG.2, hmG.1, h2, h1, [T.mp k], .cons ⟨hmG.2, h2.trans ?_⟩ (by
          show G.pω (T.mp k) ≤ T.mw k; omega) ⟨hmp, Or.inr ⟨rfl, rfl⟩⟩ (.nil ⟨hmG.1, h1.trans ?_⟩)⟩
        · have := Under.par (T := T) (T.ch1 k); rwa [hp1] at this
        · have := Under.par (T := T) (T.ch2 k); rwa [hp2] at this
    obtain ⟨a1, b2, ha1, hb2, hu1, hu2, qs, hqs⟩ := hcross
    have w1 := fun a ha hua => hin _ hlt1 hp1 a a1 ha ha1 hua hu1
    have w2 := fun b hb hub => hin _ hlt2 hp2 b2 b hb2 hb hu2 hub
    have w1' := fun b hb hub => hin _ hlt1 hp1 a1 b ha1 hb hu1 hub
    have w2' := fun a ha hua => hin _ hlt2 hp2 a b2 ha hb2 hua hu2
    rcases hchild a ha hua with hA | hA <;> rcases hchild b hb hub with hB | hB
    · exact hin _ hlt1 hp1 a b ha hb hA hB
    · obtain ⟨p1, hp1'⟩ := w1 a ha hA
      obtain ⟨p2, hp2'⟩ := w2 b hb hB
      exact ⟨p1 ++ qs ++ p2, (hp1'.append hqs).append hp2'⟩
    · obtain ⟨p1, hp1'⟩ := w2' a ha hA
      obtain ⟨p2, hp2'⟩ := w1' b hb hB
      exact ⟨p1 ++ qs.reverse ++ p2, (hp1'.append hqs.reverse).append hp2'⟩
    · exact hin _ hlt2 hp2 a b ha hb hA hB

end KT

end MinCostFlow.LowStretch
