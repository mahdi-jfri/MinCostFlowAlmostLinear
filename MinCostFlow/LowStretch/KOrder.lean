module

public import MinCostFlow.LowStretch.KClust

/-!
# Leaves, leaf order and heavy paths of a merge tree

For the cluster steps the program needs three more things about the merge tree `T`.
* The leaves below a node `k` (`lv k`) and their number `sz k`. A node has the leaves of its two
  children, which are disjoint (`lv_inner`).
* An order of the leaves in which the leaves below every node form an interval: node `k` gets
  the interval starting at `lo k` of length `sz k`. The first child starts where its parent
  starts, and the second child right after the first (`lo_ch1`, `lo_ch2`, `Under.lo`, `lo_injOn`).
* Heavy paths. The heavy child of a node is the child with more leaves (the first child on a
  tie). The head `hd k` of `k` is the highest node reached from `k` by heavy children only. Two
  nodes with the same head lie on one path (`hd_eq`). Every step to a node that is not the head
  of its child at least doubles the number of leaves (`two_sz_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace KT

variable {T : KT} {G : PG}

open Classical in
/-- The leaves below node `k`. -/
noncomputable def lv (T : KT) (G : PG) (k : ℕ) : Finset ℕ := (Finset.range G.n).filter (T.Under · k)

/-- The number of leaves below node `k`. -/
noncomputable def sz (T : KT) (G : PG) (k : ℕ) : ℕ := (T.lv G k).card

theorem mem_lv {k v : ℕ} : v ∈ T.lv G k ↔ v < G.n ∧ T.Under v k := by
  simp [lv]

theorem lv_leaf (h : T.Ok G) {v : ℕ} (hv : v < G.n) : T.lv G v = {v} := by
  have hN := h.n_lt
  ext x
  simp only [mem_lv, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hu⟩; exact under_leaf h (by omega) hv hu
  · rintro rfl; exact ⟨hv, Under.refl _⟩

theorem sz_leaf (h : T.Ok G) {v : ℕ} (hv : v < G.n) : T.sz G v = 1 := by
  rw [sz, lv_leaf h hv]; rfl

/-- A node that is not the root is a child of its parent, which is an inner node. -/
theorem child_of (h : T.Ok G) {x : ℕ} (hx : x + 1 < T.N) :
    G.n ≤ T.par x ∧ T.par x < T.N ∧ x < T.par x ∧ (x = T.ch1 (T.par x) ∨ x = T.ch2 (T.par x)) :=
  ⟨h.par_internal x hx, (h.par_lt x hx).2, (h.par_lt x hx).1, h.par_ch x hx⟩

theorem under_ch1 (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) : T.Under (T.ch1 k) k := by
  have := Under.par (T := T) (T.ch1 k); rwa [(h.ch k hkn hk).1] at this

theorem under_ch2 (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) : T.Under (T.ch2 k) k := by
  have := Under.par (T := T) (T.ch2 k); rwa [(h.ch k hkn hk).2.1] at this

theorem lv_inner (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) :
    T.lv G k = T.lv G (T.ch1 k) ∪ T.lv G (T.ch2 k) := by
  have hN := h.n_lt
  ext v
  simp only [Finset.mem_union, mem_lv]
  constructor
  · rintro ⟨hv, hu⟩
    obtain ⟨c, hvc, hpc, hck⟩ := child_on_path hu (by omega)
    have hcN : c < T.N := hvc.lt_N h (by omega)
    have hc1 : c + 1 < T.N := by
      by_contra hc
      have e : c = T.N - 1 := by omega
      rw [e, h.root] at hpc
      exact hck (e.trans hpc)
    rcases h.par_ch c hc1 with e | e <;> rw [hpc] at e
    · exact Or.inl ⟨hv, e ▸ hvc⟩
    · exact Or.inr ⟨hv, e ▸ hvc⟩
  · rintro (⟨hv, hu⟩ | ⟨hv, hu⟩)
    · exact ⟨hv, hu.trans (under_ch1 h hkn hk)⟩
    · exact ⟨hv, hu.trans (under_ch2 h hkn hk)⟩

theorem lv_disj (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) :
    Disjoint (T.lv G (T.ch1 k)) (T.lv G (T.ch2 k)) := by
  rw [Finset.disjoint_left]
  intro v h1 h2
  exact not_under_both h hkn hk (mem_lv.mp h1).2 (mem_lv.mp h2).2

theorem sz_inner (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) :
    T.sz G k = T.sz G (T.ch1 k) + T.sz G (T.ch2 k) := by
  rw [sz, lv_inner h hkn hk, Finset.card_union_of_disjoint (lv_disj h hkn hk)]; rfl

theorem Under.lv_sub {j k : ℕ} (hu : T.Under j k) : T.lv G j ⊆ T.lv G k := fun v hv =>
  mem_lv.mpr ⟨(mem_lv.mp hv).1, (mem_lv.mp hv).2.trans hu⟩

theorem Under.sz_le {j k : ℕ} (hu : T.Under j k) : T.sz G j ≤ T.sz G k :=
  Finset.card_le_card hu.lv_sub

theorem sz_le_n (k : ℕ) : T.sz G k ≤ G.n := by
  have : T.lv G k ⊆ Finset.range G.n := fun v hv => Finset.mem_range.mpr (mem_lv.mp hv).1
  exact (Finset.card_le_card this).trans (by simp)

theorem sz_pos (h : T.Ok G) {k : ℕ} (hk : k < T.N) : 1 ≤ T.sz G k := by
  obtain ⟨v, hv, hu⟩ := exists_leaf h k hk
  exact Finset.card_pos.mpr ⟨v, mem_lv.mpr ⟨hv, hu⟩⟩

theorem sz_root (h : T.Ok G) : T.sz G (T.N - 1) = G.n := by
  have e : T.lv G (T.N - 1) = Finset.range G.n := by
    ext v; simp only [mem_lv, Finset.mem_range]; exact ⟨fun h => h.1, fun hv => ⟨hv, h.all v hv⟩⟩
  rw [sz, e, Finset.card_range]

/-! ### The leaf order -/

/-- Where the interval of node `k` starts. -/
noncomputable def lo (T : KT) (G : PG) (k : ℕ) : ℕ :=
  if _ : k + 1 < T.N ∧ k < T.par k then
    if k = T.ch1 (T.par k) then T.lo G (T.par k) else T.lo G (T.par k) + T.sz G (T.ch1 (T.par k))
  else 0
termination_by T.N - k

theorem lo_root : T.lo G (T.N - 1) = 0 := by
  rw [lo, dif_neg (by omega)]

theorem lo_ch1 (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) :
    T.lo G (T.ch1 k) = T.lo G k := by
  obtain ⟨hp1, -, -, hlt1, -⟩ := h.ch k hkn hk
  rw [lo, dif_pos ⟨by omega, by omega⟩, hp1, if_pos rfl]

theorem lo_ch2 (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) :
    T.lo G (T.ch2 k) = T.lo G k + T.sz G (T.ch1 k) := by
  obtain ⟨-, hp2, hne, -, hlt2⟩ := h.ch k hkn hk
  rw [lo, dif_pos ⟨by omega, by omega⟩, hp2, if_neg (Ne.symm hne)]

theorem lo_step (h : T.Ok G) {x : ℕ} (hx : x + 1 < T.N) :
    T.lo G (T.par x) ≤ T.lo G x ∧ T.lo G x + T.sz G x ≤ T.lo G (T.par x) + T.sz G (T.par x) := by
  obtain ⟨hpn, hpN, -, hc⟩ := child_of h hx
  rw [sz_inner h hpn hpN]
  rcases hc with e | e
  · have := lo_ch1 h hpn hpN
    rw [← e] at this
    rw [this]; rw [← e]; omega
  · have := lo_ch2 h hpn hpN
    rw [← e] at this
    rw [this]; rw [← e]; omega

/-- The interval of a node lies inside the interval of every node above it. -/
theorem Under.lo (h : T.Ok G) {j k : ℕ} (hj : j < T.N) (hu : T.Under j k) :
    T.lo G k ≤ T.lo G j ∧ T.lo G j + T.sz G j ≤ T.lo G k + T.sz G k := by
  obtain ⟨i, rfl⟩ := hu
  induction i with
  | zero => exact ⟨le_rfl, le_rfl⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    set y := T.par^[i] j
    have hyN : y < T.N := iter_lt_N h hj i
    by_cases hy : y + 1 < T.N
    · have := lo_step h hy; omega
    · have e : y = T.N - 1 := by omega
      rw [e, h.root, ← e]; exact ih

theorem lo_lt (h : T.Ok G) {v : ℕ} (hv : v < G.n) : T.lo G v < G.n := by
  have hN := h.n_lt
  have := (h.all v hv).lo h (by omega)
  rw [lo_root, sz_root h, sz_leaf h hv] at this
  omega

/-- Different leaves below a node get different places in its interval. -/
theorem lo_injOn (h : T.Ok G) : ∀ k < T.N, Set.InjOn (T.lo G) (T.lv G k) := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    have hN := h.n_lt
    by_cases hkn : k < G.n
    · rw [lv_leaf h hkn]; simp
    push Not at hkn
    obtain ⟨-, -, -, hlt1, hlt2⟩ := h.ch k hkn hk
    rw [lv_inner h hkn hk]
    intro a ha b hb hab
    simp only [Finset.coe_union, Set.mem_union, Finset.mem_coe] at ha hb
    have r1 : ∀ v ∈ T.lv G (T.ch1 k), T.lo G v < T.lo G k + T.sz G (T.ch1 k) := fun v hv => by
      have := ((mem_lv.mp hv).2).lo h (by have := (mem_lv.mp hv).1; omega)
      rw [lo_ch1 h hkn hk, sz_leaf h (mem_lv.mp hv).1] at this; omega
    have r2 : ∀ v ∈ T.lv G (T.ch2 k), T.lo G k + T.sz G (T.ch1 k) ≤ T.lo G v := fun v hv => by
      have := ((mem_lv.mp hv).2).lo h (by have := (mem_lv.mp hv).1; omega)
      rw [lo_ch2 h hkn hk] at this; omega
    rcases ha with ha | ha <;> rcases hb with hb | hb
    · exact ih _ hlt1 (by omega) ha hb hab
    · have := r1 a ha; have := r2 b hb; omega
    · have := r2 a ha; have := r1 b hb; omega
    · exact ih _ hlt2 (by omega) ha hb hab

/-- The interval of a node is filled by its leaves: if `A (lo v) = v` for every leaf `v`, then
every place in the interval of `k` holds a leaf below `k`. -/
theorem lo_fill (h : T.Ok G) {A : ℕ → ℕ} (hA : ∀ v < G.n, A (T.lo G v) = v) {k j : ℕ}
    (hk : k < T.N) (hj1 : T.lo G k ≤ j) (hj2 : j < T.lo G k + T.sz G k) : A j ∈ T.lv G k := by
  classical
  have hN := h.n_lt
  have hsub : (T.lv G k).image (T.lo G) ⊆ Finset.Ico (T.lo G k) (T.lo G k + T.sz G k) := by
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    have := ((mem_lv.mp hv).2).lo h (by have := (mem_lv.mp hv).1; omega)
    rw [sz_leaf h (mem_lv.mp hv).1] at this
    exact Finset.mem_Ico.mpr ⟨this.1, by omega⟩
  have hcard : ((T.lv G k).image (T.lo G)).card = T.sz G k :=
    Finset.card_image_of_injOn (lo_injOn h k hk)
  have heq := Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; simp)
  have hjm : j ∈ (T.lv G k).image (T.lo G) := by
    rw [heq]; exact Finset.mem_Ico.mpr ⟨hj1, hj2⟩
  obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hjm
  rw [hA v (mem_lv.mp hv).1]; exact hv

/-! ### Heavy paths -/

/-- The heavy child: the child with more leaves, the first one on a tie. -/
noncomputable def heavy (T : KT) (G : PG) (k : ℕ) : ℕ :=
  if T.sz G (T.ch2 k) ≤ T.sz G (T.ch1 k) then T.ch1 k else T.ch2 k

/-- The head: the highest node reached by heavy children only. -/
noncomputable def hd (T : KT) (G : PG) (k : ℕ) : ℕ :=
  if _ : k + 1 < T.N ∧ k < T.par k then
    if k = T.heavy G (T.par k) then T.hd G (T.par k) else k
  else k
termination_by T.N - k

theorem hd_root : T.hd G (T.N - 1) = T.N - 1 := by
  rw [hd, dif_neg (by omega)]

theorem hd_heavy (h : T.Ok G) {x : ℕ} (hx : x + 1 < T.N) (hh : x = T.heavy G (T.par x)) :
    T.hd G x = T.hd G (T.par x) := by
  rw [hd, dif_pos ⟨hx, (h.par_lt x hx).1⟩, if_pos hh]

theorem hd_light (h : T.Ok G) {x : ℕ} (hx : x + 1 < T.N) (hh : x ≠ T.heavy G (T.par x)) :
    T.hd G x = x := by
  rw [hd, dif_pos ⟨hx, (h.par_lt x hx).1⟩, if_neg hh]

theorem heavy_ch1 (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) :
    T.hd G (T.heavy G k) = T.hd G k := by
  obtain ⟨hp1, hp2, -, hlt1, hlt2⟩ := h.ch k hkn hk
  unfold heavy
  split_ifs
  · rw [hd_heavy h (by omega) (by rw [hp1]; unfold heavy; rw [if_pos ‹_›]), hp1]
  · rw [hd_heavy h (by omega) (by rw [hp2]; unfold heavy; rw [if_neg ‹_›]), hp2]

/-- The light child: the other child. -/
noncomputable def light (T : KT) (G : PG) (k : ℕ) : ℕ :=
  if T.sz G (T.ch2 k) ≤ T.sz G (T.ch1 k) then T.ch2 k else T.ch1 k

theorem hd_lightc (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) :
    T.hd G (T.light G k) = T.light G k := by
  obtain ⟨hp1, hp2, hne, hlt1, hlt2⟩ := h.ch k hkn hk
  unfold light
  split_ifs with hs
  · exact hd_light h (by omega) (by rw [hp2]; unfold heavy; rw [if_pos hs]; exact Ne.symm hne)
  · exact hd_light h (by omega) (by rw [hp1]; unfold heavy; rw [if_neg hs]; exact hne)

theorem heavy_light (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) :
    (T.heavy G k = T.ch1 k ∧ T.light G k = T.ch2 k) ∨
      (T.heavy G k = T.ch2 k ∧ T.light G k = T.ch1 k) := by
  unfold heavy light; split_ifs <;> simp

theorem two_sz_light (h : T.Ok G) {k : ℕ} (hkn : G.n ≤ k) (hk : k < T.N) :
    2 * T.sz G (T.light G k) ≤ T.sz G k := by
  rw [sz_inner h hkn hk]; unfold light; split_ifs <;> omega

theorem hd_under (h : T.Ok G) : ∀ k < T.N, T.Under k (T.hd G k) := by
  intro k hk
  induction hn : T.N - k using Nat.strong_induction_on generalizing k with
  | _ d ih =>
    by_cases hc : k + 1 < T.N ∧ k < T.par k
    · by_cases hh : k = T.heavy G (T.par k)
      · rw [hd_heavy h hc.1 hh]
        have hpN := (h.par_lt k hc.1).2
        exact (Under.par k).trans (ih _ (by omega) _ hpN rfl)
      · rw [hd_light h hc.1 hh]; exact Under.refl _
    · rw [hd, dif_neg hc]; exact Under.refl _

/-- A head is the root or a light child. -/
theorem hd_cases (h : T.Ok G) : ∀ k < T.N, T.hd G k = T.N - 1 ∨
    (T.hd G k + 1 < T.N ∧ T.hd G k ≠ T.heavy G (T.par (T.hd G k))) := by
  intro k hk
  induction hn : T.N - k using Nat.strong_induction_on generalizing k with
  | _ d ih =>
    by_cases hc : k + 1 < T.N
    · have hpk := (h.par_lt k hc).1
      by_cases hh : k = T.heavy G (T.par k)
      · rw [hd_heavy h hc hh]
        exact ih _ (by omega) _ (h.par_lt k hc).2 rfl
      · rw [hd_light h hc hh]; exact Or.inr ⟨hc, hh⟩
    · have e : k = T.N - 1 := by omega
      subst e; rw [hd_root]; exact Or.inl rfl

/-- The step above a head at least doubles the number of leaves. -/
theorem two_sz_le (h : T.Ok G) {k : ℕ} (hk : k < T.N) (hr : T.hd G k + 1 < T.N) :
    2 * T.sz G k ≤ T.sz G (T.par (T.hd G k)) := by
  rcases hd_cases h k hk with e | ⟨-, hne⟩
  · omega
  · obtain ⟨hpn, hpN, -, hc⟩ := child_of h hr
    have hl : T.hd G k = T.light G (T.par (T.hd G k)) := by
      rcases heavy_light h hpn hpN with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hc with c | c <;>
        rw [e1] at hne <;> rw [e2] <;> first | exact absurd c hne | exact c
    have := two_sz_light h hpn hpN
    rw [← hl] at this
    have := (hd_under h k hk).sz_le (G := G)
    omega

/-- Along the way from `a` up to its head, the head does not change. -/
theorem hd_path (h : T.Ok G) {a : ℕ} (ha : a < T.N) :
    ∀ i, T.Under (T.par^[i] a) (T.hd G a) → T.hd G (T.par^[i] a) = T.hd G a := by
  intro i
  induction i with
  | zero => intro _; rfl
  | succ i ih =>
    intro hu
    rw [Function.iterate_succ_apply'] at hu ⊢
    set y := T.par^[i] a
    have hyN : y < T.N := iter_lt_N h ha i
    have ih' := ih ((Under.par y).trans hu)
    by_cases hy : y = T.hd G a
    · -- the parent of the head is above the head, so they are equal
      have h1 := hu.le h (par_lt_N h hyN)
      have h2 := le_par h hyN
      rw [← hy] at h1
      have : T.par y = y := le_antisymm h1 h2
      rw [this]; exact ih'
    · have hne : T.hd G y ≠ y := by rw [ih']; exact Ne.symm hy
      by_cases hc : y + 1 < T.N ∧ y < T.par y
      · by_cases hh : y = T.heavy G (T.par y)
        · rw [← hd_heavy h hc.1 hh]; exact ih'
        · exact absurd (hd_light h hc.1 hh) hne
      · rw [hd, dif_neg hc] at hne; exact absurd rfl hne

/-- A node strictly between `a` and its head is a heavy child. -/
theorem heavy_of_path (h : T.Ok G) {a x : ℕ} (ha : a < T.N) (h1 : T.Under a x)
    (h2 : T.Under x (T.hd G a)) (hx : x ≠ T.hd G a) :
    x + 1 < T.N ∧ x = T.heavy G (T.par x) := by
  obtain ⟨i, rfl⟩ := h1
  have he := hd_path h ha i h2
  set y := T.par^[i] a
  have hne : T.hd G y ≠ y := by rw [he]; exact Ne.symm hx
  by_cases hc : y + 1 < T.N ∧ y < T.par y
  · by_cases hh : y = T.heavy G (T.par y)
    · exact ⟨hc.1, hh⟩
    · exact absurd (hd_light h hc.1 hh) hne
  · rw [hd, dif_neg hc] at hne; exact absurd rfl hne

theorem under_antisymm (h : T.Ok G) {x y : ℕ} (hx : x < T.N) (h1 : T.Under x y)
    (h2 : T.Under y x) : x = y :=
  le_antisymm (h1.le h hx) (h2.le h (h1.lt_N h hx))

/-- **Two nodes with the same head lie on one path.** -/
theorem hd_eq (h : T.Ok G) {a b : ℕ} (ha : a < T.N) (hb : b < T.N) (he : T.hd G a = T.hd G b) :
    T.Under a b ∨ T.Under b a := by
  classical
  by_contra hno
  push Not at hno
  obtain ⟨hab, hba⟩ := hno
  set t := T.hd G a with ht
  have hua := hd_under h a ha
  have hub := hd_under h b hb
  rw [← he] at hub
  have hex : ∃ i, T.Under b (T.par^[i] a) := by
    obtain ⟨i, hi⟩ := hua; exact ⟨i, hi ▸ hub⟩
  have hi : T.Under b (T.par^[Nat.find hex] a) := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, ¬ T.Under b (T.par^[j] a) := fun j hj => Nat.find_min hex hj
  obtain ⟨j, hj0⟩ : ∃ j, Nat.find hex = j + 1 := by
    rcases hfe : Nat.find hex with _ | j
    · rw [hfe] at hi; exact absurd hi hba
    · exact ⟨j, rfl⟩
  rw [hj0] at hi hmin
  have hj := hmin j (by omega)
  set ca := T.par^[j] a with hca
  have hl : T.par^[j + 1] a = T.par ca := Function.iterate_succ_apply' _ _ _
  rw [hl] at hi
  set l := T.par ca with hldef
  have hcaN : ca < T.N := iter_lt_N h ha j
  have hlN : l < T.N := par_lt_N h hcaN
  have hual : T.Under a l := ⟨j + 1, hl⟩
  have huaca : T.Under a ca := ⟨j, rfl⟩
  have hcal : T.Under ca l := Under.par ca
  have hcane : ca ≠ l := fun e => hj (by rw [e]; exact hi)
  have hbl : b ≠ l := fun e => hab (e ▸ hual)
  obtain ⟨cb, hbcb, hpcb, hcbl⟩ := child_on_path hi hbl
  have hne : ca ≠ cb := fun e => hj (e ▸ hbcb)
  -- `l` lies below the head
  have hlt : T.Under l t := by
    rcases Under.total hual hua with hu | hu
    · exact hu
    · -- the head is below `l`; it is not strictly below, else it would be below `ca`
      by_cases htl : t = l
      · rw [htl]; exact Under.refl _
      · exfalso
        rcases Under.total huaca hua with hu' | hu'
        · -- `ca` below `t` below `l = par ca`, `t ≠ ca`
          by_cases htca : t = ca
          · exact hj (htca ▸ hub)
          · have := hu'.par_of_ne h (Ne.symm htca)
            exact htl (under_antisymm h (hua.lt_N h ha) hu this)
        · exact hj (hub.trans hu')
  have hlle : l ≤ t := hlt.le h hlN
  have hcalt : ca < l := lt_of_le_of_ne (le_par h hcaN) hcane
  have hcbN : cb < T.N := hbcb.lt_N h hb
  have hcblt : cb < l := by
    rw [← hpcb]; exact lt_of_le_of_ne (le_par h hcbN) (by rw [hpcb]; exact hcbl)
  have e1 := (heavy_of_path h ha huaca (hcal.trans hlt) (by omega)).2
  have hcbt : T.Under cb t := by
    have := Under.par (T := T) cb; rw [hpcb] at this; exact this.trans hlt
  have e2 := (heavy_of_path h hb hbcb (by rw [← he]; exact hcbt) (by rw [← he]; omega)).2
  rw [← hldef] at e1
  rw [hpcb] at e2
  exact hne (e1.trans e2.symm)

end KT

end MinCostFlow.LowStretch
