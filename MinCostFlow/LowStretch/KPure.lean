module

public import MinCostFlow.LowStretch.KTree

/-!
# Kruskal's merge tree, as a function

`kstep` processes one pair: if its ends lie under two different current tops `a` and `b`, it adds
a node `N` with children `a` and `b`, the pair's weight and the pair. `krun` processes a list of
pairs. If the list is sorted by weight and has, for every pair of the graph, a pair with the same
ends that is at least as light, the result is a merge tree (`krun_ok`).

The program of `ProgKruskal` computes `krun` with a union-find structure.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- A merge tree under construction, with the current top of every vertex. -/
structure KS where
  T : KT
  top : ℕ → ℕ

variable (G : PG)

/-- The start: every vertex is its own top. -/
def kinit : KS :=
  ⟨⟨G.n, id, fun _ => 0, fun _ => 0, fun _ => 0, fun _ => 0⟩, id⟩

/-- Process pair `q`. -/
def kstep (s : KS) (q : ℕ) : KS :=
  let a := s.top (G.pu q)
  let b := s.top (G.pv q)
  if a = b then s else
  { T := { N := s.T.N + 1
           par := fun k => if k = a ∨ k = b then s.T.N else s.T.par k
           ch1 := Function.update s.T.ch1 s.T.N a
           ch2 := Function.update s.T.ch2 s.T.N b
           mw := Function.update s.T.mw s.T.N (G.pω q)
           mp := Function.update s.T.mp s.T.N q }
    top := fun x => if s.top x = a ∨ s.top x = b then s.T.N else s.top x }

/-- Process a list of pairs. -/
def krun (L : List ℕ) : KS := L.foldl (kstep G) (kinit G)

namespace KS

variable {G}

/-- Changing the parent only at nodes that were their own parents keeps every path. -/
theorem under_mono {par par' : ℕ → ℕ} (hpar : ∀ k, par k ≠ k → par' k = par k) {x y : ℕ}
    (hu : ∃ i, par^[i] x = y) : ∃ i, par'^[i] x = y := by
  obtain ⟨i, hi⟩ := hu
  induction i generalizing x with
  | zero => exact ⟨0, hi⟩
  | succ i ih =>
    by_cases hx : par x = x
    · have : par^[i + 1] x = x := Function.iterate_fixed hx _
      exact ⟨0, by rw [← hi, this]; rfl⟩
    · rw [Function.iterate_succ_apply] at hi
      obtain ⟨j, hj⟩ := ih hi
      exact ⟨j + 1, by rw [Function.iterate_succ_apply, hpar x hx, hj]⟩

/-- A path in the new tree to a node other than the new one is a path in the old tree, when the
new parent of the changed nodes is a fixed point. -/
theorem under_back {par par' : ℕ → ℕ} {N : ℕ} (hpar : ∀ k, par' k ≠ par k → par' k = N)
    (hN : par' N = N) {x y : ℕ} (hy : y ≠ N) (hu : ∃ i, par'^[i] x = y) : ∃ i, par^[i] x = y := by
  obtain ⟨i, hi⟩ := hu
  induction i generalizing x with
  | zero => exact ⟨0, hi⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply] at hi
    by_cases hx : par' x = par x
    · rw [hx] at hi
      obtain ⟨j, hj⟩ := ih hi
      exact ⟨j + 1, by rw [Function.iterate_succ_apply, hj]⟩
    · rw [hpar x hx, Function.iterate_fixed hN] at hi
      exact absurd hi.symm hy

variable (G) in
/-- The invariant of the construction, after the pairs `l`, with the pairs `r` still to come. -/
structure Inv (s : KS) (l r : List ℕ) : Prop where
  n_le : G.n ≤ s.T.N
  par_big : ∀ k, s.T.N ≤ k → s.T.par k = k
  par_lt : ∀ k < s.T.N, s.T.par k < s.T.N ∧ k ≤ s.T.par k
  is_top : ∀ k < s.T.N, s.T.par k = k → ∃ v < G.n, s.top v = k
  top : ∀ v < G.n, s.top v < s.T.N ∧ s.T.Under v (s.top v) ∧ s.T.par (s.top v) = s.top v
  par_ch : ∀ k < s.T.N, s.T.par k ≠ k → G.n ≤ s.T.par k ∧
    (k = s.T.ch1 (s.T.par k) ∨ k = s.T.ch2 (s.T.par k))
  ch : ∀ k, G.n ≤ k → k < s.T.N → s.T.par (s.T.ch1 k) = k ∧ s.T.par (s.T.ch2 k) = k ∧
    s.T.ch1 k ≠ s.T.ch2 k ∧ s.T.ch1 k < k ∧ s.T.ch2 k < k
  leaf_mw : ∀ v < G.n, s.T.mw v = 0
  mw_mono : ∀ k < s.T.N, s.T.mw k ≤ s.T.mw (s.T.par k)
  merge : ∀ k, G.n ≤ k → k < s.T.N → s.T.mp k < G.m ∧ G.pω (s.T.mp k) = s.T.mw k ∧
    s.T.Splits G (s.T.mp k) k
  lca : ∀ p < G.m, ∀ k, G.n ≤ k → k < s.T.N → s.T.Splits G p k → s.T.mw k ≤ G.pω p
  done : ∀ q ∈ l, s.top (G.pu q) = s.top (G.pv q)
  later : ∀ k < s.T.N, ∀ q ∈ r, s.T.mw k ≤ G.pω q
  last : s.T.par (s.T.N - 1) = s.T.N - 1

theorem under_fixed {T : KT} {t y : ℕ} (ht : T.par t = t) (h : T.Under t y) : y = t := by
  obtain ⟨i, hi⟩ := h
  rw [Function.iterate_fixed ht] at hi
  exact hi.symm

/-- A vertex is under a top exactly when that top is its top. -/
theorem under_top_iff {s : KS} {l r : List ℕ} (h : s.Inv G l r) {x t : ℕ} (hx : x < G.n)
    (ht : s.T.par t = t) : s.T.Under x t ↔ s.top x = t := by
  obtain ⟨-, hu, hp⟩ := h.top x hx
  constructor
  · intro hxt
    rcases KT.Under.total hxt hu with h1 | h1
    · exact (under_fixed ht h1)
    · exact (under_fixed hp h1).symm
  · intro e; rw [← e]; exact hu

/-- The ends of two pairs are the same, in some order. -/
def SameEnds (G : PG) (p r : ℕ) : Prop :=
  (G.pu r = G.pu p ∧ G.pv r = G.pv p) ∨ (G.pu r = G.pv p ∧ G.pv r = G.pu p)

/-- One step keeps the invariant. `hcov` says that every pair has a representative in the whole
list `l ++ q :: r` that is at least as light, and `hsort` that `q` is at most as heavy as the
pairs after it. -/
theorem Inv.step {s : KS} {l r : List ℕ} {q : ℕ} (h : s.Inv G l (q :: r))
    (hq : G.pu q < G.n ∧ G.pv q < G.n) (hqm : q < G.m)
    (hcov : ∀ p < G.m, ∃ r0 ∈ l ++ q :: r, SameEnds G p r0 ∧ G.pω r0 ≤ G.pω p)
    (hsort : ∀ q' ∈ r, G.pω q ≤ G.pω q') (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) :
    (kstep G s q).Inv G (l ++ [q]) r := by
  have hlater : ∀ k < s.T.N, ∀ q' ∈ r, s.T.mw k ≤ G.pω q' := fun k hk q' hq' =>
    h.later k hk q' (List.mem_cons_of_mem _ hq')
  unfold kstep
  set a := s.top (G.pu q) with ha_def
  set b := s.top (G.pv q) with hb_def
  by_cases hab : a = b
  · rw [if_pos hab]
    exact { h with
      last := h.last
      done := fun q' hq' => by
        rcases List.mem_append.mp hq' with hq' | hq'
        · exact h.done q' hq'
        · simp at hq'; subst hq'; exact hab
      later := hlater }
  rw [if_neg hab]
  obtain ⟨haN, hua, hpa⟩ := h.top _ hq.1
  obtain ⟨hbN, hub, hpb⟩ := h.top _ hq.2
  rw [← ha_def] at haN hua hpa
  rw [← hb_def] at hbN hub hpb
  set N := s.T.N with hN_def
  have hpN : s.T.par N = N := h.par_big N le_rfl
  have haN' : a ≠ N := by omega
  have hbN' : b ≠ N := by omega
  -- the new parent function
  set par' : ℕ → ℕ := fun k => if k = a ∨ k = b then N else s.T.par k with hpar'
  have hp1 : ∀ k, s.T.par k ≠ k → par' k = s.T.par k := fun k hk => by
    simp only [hpar']
    rw [if_neg]
    rintro (rfl | rfl)
    · exact hk hpa
    · exact hk hpb
  have hp2 : ∀ k, par' k ≠ s.T.par k → par' k = N := fun k hk => by
    simp only [hpar'] at hk ⊢
    split_ifs at hk ⊢ with h' <;> simp_all
  have hpN' : par' N = N := by simp only [hpar']; rw [if_neg (by omega)]; exact hpN
  have U1 : ∀ x y, s.T.Under x y → ∃ i, par'^[i] x = y := fun x y hu => under_mono hp1 hu
  have U2 : ∀ x y, y ≠ N → (∃ i, par'^[i] x = y) → s.T.Under x y := fun x y hy hu =>
    under_back hp2 hpN' hy hu
  have hch1 : ∀ k, k ≠ N → Function.update s.T.ch1 N a k = s.T.ch1 k := fun k hk => by
    rw [Function.update_apply, if_neg hk]
  have hch2 : ∀ k, k ≠ N → Function.update s.T.ch2 N b k = s.T.ch2 k := fun k hk => by
    rw [Function.update_apply, if_neg hk]
  -- splits at old nodes do not change
  have hSold : ∀ p k, G.n ≤ k → k < N →
      (((∃ i, par'^[i] (G.pu p) = Function.update s.T.ch1 N a k) ∧
        (∃ i, par'^[i] (G.pv p) = Function.update s.T.ch2 N b k) ∨
       (∃ i, par'^[i] (G.pu p) = Function.update s.T.ch2 N b k) ∧
        (∃ i, par'^[i] (G.pv p) = Function.update s.T.ch1 N a k)) ↔ s.T.Splits G p k) := by
    intro p k hk1 hk2
    obtain ⟨-, -, -, c1, c2⟩ := h.ch k hk1 hk2
    rw [hch1 k (by omega), hch2 k (by omega)]
    unfold KT.Splits
    constructor
    · rintro (⟨x1, x2⟩ | ⟨x1, x2⟩)
      · exact Or.inl ⟨U2 _ _ (by omega) x1, U2 _ _ (by omega) x2⟩
      · exact Or.inr ⟨U2 _ _ (by omega) x1, U2 _ _ (by omega) x2⟩
    · rintro (⟨x1, x2⟩ | ⟨x1, x2⟩)
      · exact Or.inl ⟨U1 _ _ x1, U1 _ _ x2⟩
      · exact Or.inr ⟨U1 _ _ x1, U1 _ _ x2⟩
  -- splits at the new node
  have hSnew : ∀ p, G.pu p < G.n → G.pv p < G.n →
      (((∃ i, par'^[i] (G.pu p) = Function.update s.T.ch1 N a N) ∧
        (∃ i, par'^[i] (G.pv p) = Function.update s.T.ch2 N b N) ∨
       (∃ i, par'^[i] (G.pu p) = Function.update s.T.ch2 N b N) ∧
        (∃ i, par'^[i] (G.pv p) = Function.update s.T.ch1 N a N)) ↔
      (s.top (G.pu p) = a ∧ s.top (G.pv p) = b ∨ s.top (G.pu p) = b ∧ s.top (G.pv p) = a)) := by
    intro p hpu hpv
    simp only [Function.update_self]
    rw [← under_top_iff h hpu hpa, ← under_top_iff h hpv hpb, ← under_top_iff h hpu hpb,
      ← under_top_iff h hpv hpa]
    constructor
    · rintro (⟨x1, x2⟩ | ⟨x1, x2⟩)
      · exact Or.inl ⟨U2 _ _ haN' x1, U2 _ _ hbN' x2⟩
      · exact Or.inr ⟨U2 _ _ hbN' x1, U2 _ _ haN' x2⟩
    · rintro (⟨x1, x2⟩ | ⟨x1, x2⟩)
      · exact Or.inl ⟨U1 _ _ x1, U1 _ _ x2⟩
      · exact Or.inr ⟨U1 _ _ x1, U1 _ _ x2⟩
  have ucomp : ∀ x y z, (∃ i, par'^[i] x = y) → (∃ i, par'^[i] y = z) → ∃ i, par'^[i] x = z := by
    rintro x y z ⟨i, rfl⟩ ⟨j, rfl⟩
    exact ⟨j + i, by rw [Function.iterate_add_apply]⟩
  have hab' : ∀ k, k = a ∨ k = b → par' k = N := fun k hk => by simp only [hpar']; rw [if_pos hk]
  have hnab : ∀ k, ¬ (k = a ∨ k = b) → par' k = s.T.par k := fun k hk => by
    simp only [hpar']; rw [if_neg hk]
  refine ⟨by show G.n ≤ N + 1; have := h.n_le; omega, fun k hk => ?_, fun k hk => ?_, fun k hk hkk => ?_, fun v hv => ?_,
    fun k hk hkk => ?_, fun k hk1 hk2 => ?_, fun v hv => ?_, fun k hk => ?_, fun k hk1 hk2 => ?_,
    fun p hp k hk1 hk2 hspl => ?_, fun q' hq' => ?_, fun k hk q' hq' => ?_, ?_⟩
  · -- par_big
    simp only at hk ⊢
    rw [hnab k (by omega)]; exact h.par_big k (by omega)
  · -- par_lt
    simp only at hk ⊢
    by_cases hk' : k = a ∨ k = b
    · rw [hab' k hk']; rcases hk' with rfl | rfl <;> omega
    · rw [hnab k hk']
      by_cases hkN : k = N
      · subst hkN; rw [hpN]; omega
      · have := h.par_lt k (by omega); omega
  · -- is_top
    simp only at hk hkk ⊢
    by_cases hkN : k = N
    · subst hkN
      exact ⟨G.pu q, hq.1, by rw [if_pos (Or.inl ha_def.symm)]⟩
    · have hk' : ¬ (k = a ∨ k = b) := fun hk' => by rw [hab' k hk'] at hkk; exact hkN hkk.symm
      rw [hnab k hk'] at hkk
      obtain ⟨v, hv, hvk⟩ := h.is_top k (by omega) hkk
      exact ⟨v, hv, by rw [if_neg (by rw [hvk]; exact hk'), hvk]⟩
  · -- top
    simp only
    obtain ⟨t1, t2, t3⟩ := h.top v hv
    by_cases hv' : s.top v = a ∨ s.top v = b
    · rw [if_pos hv']
      exact ⟨by omega, ucomp _ _ _ (U1 _ _ t2) ⟨1, by simp [hab' _ hv']⟩, hpN'⟩
    · rw [if_neg hv']
      exact ⟨by omega, U1 _ _ t2, by rw [hnab _ hv', t3]⟩
  · -- par_ch
    simp only at hk hkk ⊢
    by_cases hk' : k = a ∨ k = b
    · rw [hab' k hk']
      refine ⟨h.n_le, ?_⟩
      simp only [Function.update_self]
      rcases hk' with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    · rw [hnab k hk'] at hkk ⊢
      have hkN : k ≠ N := fun e => by subst e; exact hkk hpN
      obtain ⟨c1, c2⟩ := h.par_ch k (by omega) hkk
      have := (h.par_lt k (by omega)).1
      rw [hch1 _ (by omega), hch2 _ (by omega)]
      exact ⟨c1, c2⟩
  · -- ch
    simp only at hk2 ⊢
    by_cases hkN : k = N
    · subst hkN
      simp only [Function.update_self]
      exact ⟨hab' a (Or.inl rfl), hab' b (Or.inr rfl), hab, by omega, by omega⟩
    · rw [hch1 _ hkN, hch2 _ hkN]
      obtain ⟨c1, c2, c3, c4, c5⟩ := h.ch k hk1 (by omega)
      have n1 : ¬ (s.T.ch1 k = a ∨ s.T.ch1 k = b) := by
        rintro (e | e)
        · rw [e, hpa] at c1; omega
        · rw [e, hpb] at c1; omega
      have n2 : ¬ (s.T.ch2 k = a ∨ s.T.ch2 k = b) := by
        rintro (e | e)
        · rw [e, hpa] at c2; omega
        · rw [e, hpb] at c2; omega
      exact ⟨by rw [hnab _ n1, c1], by rw [hnab _ n2, c2], c3, c4, c5⟩
  · -- leaf_mw
    simp only
    rw [Function.update_apply, if_neg (by have := h.n_le; omega)]
    exact h.leaf_mw v hv
  · -- mw_mono
    simp only at hk ⊢
    by_cases hkN : k = N
    · subst hkN; rw [hpN']
    by_cases hk' : k = a ∨ k = b
    · rw [hab' k hk', Function.update_self, Function.update_apply, if_neg hkN]
      exact h.later k (by omega) q (by simp)
    · rw [hnab k hk', Function.update_apply, if_neg hkN, Function.update_apply,
        if_neg (by have := (h.par_lt k (by omega)).1; omega)]
      exact h.mw_mono k (by omega)
  · -- merge
    simp only at hk2 ⊢
    by_cases hkN : k = N
    · subst hkN
      simp only [Function.update_self]
      refine ⟨hqm, by simp, ?_⟩
      exact (hSnew q hq.1 hq.2).mpr (Or.inl ⟨rfl, rfl⟩)
    · rw [Function.update_apply, if_neg hkN, Function.update_apply, if_neg hkN]
      obtain ⟨m1, m2, m3⟩ := h.merge k hk1 (by omega)
      exact ⟨m1, m2, (hSold _ k hk1 (by omega)).mpr m3⟩
  · -- lca
    simp only at hk2 hspl ⊢
    by_cases hkN : k = N
    · subst hkN
      rw [Function.update_self]
      have hends := hG p hp
      have ht := (hSnew p hends.1 hends.2).mp hspl
      obtain ⟨r0, hr0, hse, hle⟩ := hcov p hp
      rcases List.mem_append.mp hr0 with hr0 | hr0
      · have hd := h.done r0 hr0
        exfalso
        rcases hse with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rw [e1, e2] at hd <;> rcases ht with ⟨t1, t2⟩ | ⟨t1, t2⟩ <;>
          simp_all
      · rcases List.mem_cons.mp hr0 with rfl | hr0
        · exact hle
        · exact (hsort r0 hr0).trans hle
    · rw [Function.update_apply, if_neg hkN]
      exact h.lca p hp k hk1 (by omega) ((hSold p k hk1 (by omega)).mp hspl)
  · -- done
    simp only
    rcases List.mem_append.mp hq' with hq' | hq'
    · rw [h.done q' hq']
    · simp at hq'; subst hq'
      rw [if_pos (Or.inl ha_def.symm), if_pos (Or.inr hb_def.symm)]
  · -- later
    simp only at hk ⊢
    by_cases hkN : k = N
    · subst hkN; rw [Function.update_self]; exact hsort q' hq'
    · rw [Function.update_apply, if_neg hkN]; exact hlater k (by omega) q' hq'
  · -- last
    show par' (N + 1 - 1) = N + 1 - 1
    rw [show N + 1 - 1 = N by omega]; exact hpN'

theorem inv_init (L : List ℕ) : (kinit G).Inv G [] L where
  n_le := le_rfl
  par_big := fun _ _ => rfl
  par_lt := fun k hk => ⟨hk, le_rfl⟩
  is_top := fun k hk _ => ⟨k, hk, rfl⟩
  top := fun v hv => ⟨hv, KT.Under.refl _, rfl⟩
  par_ch := fun k _ hk => absurd rfl hk
  ch := fun k hk1 hk2 => absurd hk2 (by simp [kinit]; omega)
  leaf_mw := fun _ _ => rfl
  mw_mono := fun _ _ => le_rfl
  merge := fun k hk1 hk2 => absurd hk2 (by simp [kinit]; omega)
  lca := fun _ _ k hk1 hk2 => absurd hk2 (by simp [kinit]; omega)
  done := fun _ hq => by simp at hq
  later := fun _ _ _ _ => Nat.zero_le _
  last := rfl

/-- The whole run keeps the invariant. -/
theorem inv_run {L : List ℕ} (hL : ∀ q ∈ L, q < G.m) (hsort : L.Pairwise (G.pω · ≤ G.pω ·))
    (hcov : ∀ p < G.m, ∃ r0 ∈ L, SameEnds G p r0 ∧ G.pω r0 ≤ G.pω p)
    (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) : (krun G L).Inv G L [] := by
  suffices ∀ r l s, l ++ r = L → s.Inv G l r → (r.foldl (kstep G) s).Inv G L [] by
    exact this L [] (kinit G) (by simp) (inv_init L)
  intro r
  induction r with
  | nil => intro l s hl h; simp at hl; subst hl; exact h
  | cons q r ih =>
    intro l s hl h
    have hqL : q ∈ L := by rw [← hl]; simp
    have hqm := hL q hqL
    have hs : ∀ q' ∈ r, G.pω q ≤ G.pω q' := by
      rw [← hl] at hsort
      have := (List.pairwise_append.mp hsort).2.1
      exact (List.pairwise_cons.mp this).1
    have h' := h.step (hG q hqm) hqm (fun p hp => by rw [hl]; exact hcov p hp) hs hG
    exact ih (l ++ [q]) _ (by rw [← hl]; simp) h'

/-- After the run, the ends of every pair have the same top. -/
theorem Inv.joined {s : KS} {L : List ℕ} (h : s.Inv G L [])
    (hcov : ∀ p < G.m, ∃ r0 ∈ L, SameEnds G p r0 ∧ G.pω r0 ≤ G.pω p) {p a b : ℕ}
    (hp : G.Joins p a b) : s.top a = s.top b := by
  obtain ⟨hpm, hab⟩ := hp
  obtain ⟨r0, hr0, hse, -⟩ := hcov p hpm
  have hd := h.done r0 hr0
  rcases hse with ⟨e1, e2⟩ | ⟨e1, e2⟩ <;> rcases hab with ⟨f1, f2⟩ | ⟨f1, f2⟩ <;>
    rw [e1, e2] at hd <;> rw [f1, f2] at hd <;> first | exact hd | exact hd.symm

theorem Inv.walk {s : KS} {L : List ℕ} (h : s.Inv G L [])
    (hcov : ∀ p < G.m, ∃ r0 ∈ L, SameEnds G p r0 ∧ G.pω r0 ≤ G.pω p) {V P : Set ℕ} {a c : ℕ}
    {ps : List ℕ} (hw : G.IsWalk V P a c ps) : s.top a = s.top c := by
  induction hw with
  | nil => rfl
  | cons _ _ hj _ ih => exact (h.joined hcov hj).trans ih

/-- The run gives a merge tree when the graph is connected and has two vertices. -/
theorem krun_ok {L : List ℕ} (hL : ∀ q ∈ L, q < G.m) (hsort : L.Pairwise (G.pω · ≤ G.pω ·))
    (hcov : ∀ p < G.m, ∃ r0 ∈ L, SameEnds G p r0 ∧ G.pω r0 ≤ G.pω p)
    (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n)
    (hconn : ∀ v < G.n, G.Reach ↑(Finset.range G.n) 0 v) (hn : 2 ≤ G.n) :
    (krun G L).T.Ok G := by
  have h := inv_run hL hsort hcov hG
  set s := krun G L
  have hall : ∀ v < G.n, s.top v = s.top 0 := fun v hv => by
    obtain ⟨ps, hps⟩ := hconn v hv
    exact (h.walk hcov hps).symm
  have hN1 : s.T.N - 1 < s.T.N := by have := h.n_le; omega
  obtain ⟨v1, hv1, hv1t⟩ := h.is_top _ hN1 h.last
  have htop : ∀ v < G.n, s.top v = s.T.N - 1 := fun v hv => by rw [hall v hv, ← hall v1 hv1, hv1t]
  have hfix : ∀ k < s.T.N, s.T.par k = k → k = s.T.N - 1 := fun k hk hkk => by
    obtain ⟨v, hv, hvk⟩ := h.is_top k hk hkk
    rw [← hvk, htop v hv]
  refine ⟨?_, fun k hk => ?_, h.last, h.leaf_mw, h.mw_mono, fun k hk => ?_, fun k hk => ?_, h.ch,
    h.merge, h.lca, fun v hv => by rw [← htop v hv]; exact (h.top v hv).2.1⟩
  · -- two vertices under one top force a merge
    by_contra hlt
    have hNn : s.T.N = G.n := le_antisymm (by omega) h.n_le
    have hleaf : ∀ k < s.T.N, s.T.par k = k := fun k hk => by
      by_contra hne
      have := (h.par_ch k hk hne).1
      have := (h.par_lt k hk).1
      omega
    have h0 : s.top 0 = 0 := by
      obtain ⟨t1, t2, -⟩ := h.top 0 (by omega)
      exact under_fixed (hleaf 0 (by omega)) t2
    have h1 : s.top 1 = 1 := by
      obtain ⟨t1, t2, -⟩ := h.top 1 (by omega)
      exact under_fixed (hleaf 1 (by omega)) t2
    have := hall 1 (by omega)
    omega
  · have hne : s.T.par k ≠ k := fun e => by have := hfix k (by omega) e; omega
    have := h.par_lt k (by omega)
    exact ⟨by omega, this.1⟩
  · have hne : s.T.par k ≠ k := fun e => by have := hfix k (by omega) e; omega
    exact (h.par_ch k (by omega) hne).1
  · have hne : s.T.par k ≠ k := fun e => by have := hfix k (by omega) e; omega
    exact (h.par_ch k (by omega) hne).2

end KS

end MinCostFlow.LowStretch
