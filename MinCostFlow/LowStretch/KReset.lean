module

public import MinCostFlow.LowStretch.KClust
public import MinCostFlow.LowStretch.Contract

/-!
# The threshold of a reset, with no search

When a child `r` is reset, the program does not search for its new threshold. It takes
`θ' = thr S B s`, a power of two with `4 B s θ' ≤ S < 8 B s θ'`, where `s = |X|` and
`S = max(Δ_r, μ, 4 B s)`. Here `μ` is the largest weight of a `θ`-node of `r`. The rule `Next`
then holds (`Cl.next_reset`), for three reasons.
* Lowering the threshold and undoing the halvings only makes pairs longer, so `Δ_r ≤ Δ'`
  (`Cl.Δ_le_reset`).
* The `θ`-node of weight `μ` is split at `θ'`. Every walk between its two parts uses a pair of
  weight at least `μ`, so `μ ≤ 2 Δ'` (`Cl.mw_le_two_Δ`).
* A shortest walk of `r`, with its light pairs replaced by walks inside their `θ`-nodes, shows
  `Δ' ≤ 2 Δ_r + s μ` (`Cl.Δ_le_two_mw`).

The first cluster is handled the same way, with `S = max(μ, 4 B n)` for the weight `μ` of the
root of the Kruskal tree (`root_inv`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

/-- The new threshold: a power of two with `4 B s θ' ≤ S < 8 B s θ'`. -/
def thr (S B s : ℕ) : ℕ := 2 ^ Nat.log 2 (S / (4 * B * s))

theorem one_le_thr (S B s : ℕ) : 1 ≤ thr S B s := Nat.one_le_two_pow

theorem thr_le {S B s : ℕ} (hS : 4 * B * s ≤ S) : 4 * B * s * thr S B s ≤ S := by
  rcases Nat.eq_zero_or_pos (4 * B * s) with h0 | hq
  · rw [h0]; simp
  have hM : 1 ≤ S / (4 * B * s) := (Nat.one_le_div_iff hq).mpr hS
  have h1 : thr S B s ≤ S / (4 * B * s) := Nat.pow_log_le_self 2 (by omega)
  calc 4 * B * s * thr S B s ≤ 4 * B * s * (S / (4 * B * s)) := Nat.mul_le_mul_left _ h1
    _ ≤ S := Nat.mul_div_le S (4 * B * s)

theorem lt_thr {S B s : ℕ} (hq : 0 < 4 * B * s) : S < 8 * B * s * thr S B s := by
  have h1 : S / (4 * B * s) < 2 * thr S B s := by
    have := Nat.lt_pow_succ_log_self (b := 2) (by norm_num) (S / (4 * B * s))
    rw [pow_succ] at this
    unfold thr
    omega
  have h2 := Nat.div_add_mod S (4 * B * s)
  have h3 := Nat.mod_lt S hq
  have h4 : 4 * B * s * (S / (4 * B * s) + 1) ≤ 4 * B * s * (2 * thr S B s) :=
    Nat.mul_le_mul_left _ h1
  have e : 8 * B * s * thr S B s = 4 * B * s * (2 * thr S B s) := by ring
  rw [e]
  have : 4 * B * s * (S / (4 * B * s) + 1) = 4 * B * s * (S / (4 * B * s)) + 4 * B * s := by ring
  omega

namespace Cl

open KT

variable {T : KT} {G : PG} {P : Par}

/-- **A split node gives a lower bound on the radius.** If a cluster with nothing halved holds a
whole node `k` made by a merge, and its threshold is at most the weight of `k`, then its radius is
at least half that weight. -/
theorem mw_le_two_Δ (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) {c : Cl}
    (hc : c.Conn G) (hhalf : c.half = ∅) {k : ℕ} (hkn : G.n ≤ k) (hkN : k < T.N)
    (hsub : ∀ v < G.n, T.Under v k → v ∈ c.X) (hθ : c.θ ≤ T.mw k) : T.mw k ≤ 2 * c.Δ G := by
  obtain ⟨hp1, hp2, -, hlt1, hlt2⟩ := h.ch k hkn hkN
  obtain ⟨a, ha, hua⟩ := exists_leaf h (T.ch1 k) (by omega)
  obtain ⟨b, hb, hub⟩ := exists_leaf h (T.ch2 k) (by omega)
  have hk1 : T.Under (T.ch1 k) k := by have := Under.par (T := T) (T.ch1 k); rwa [hp1] at this
  have hk2 : T.Under (T.ch2 k) k := by have := Under.par (T := T) (T.ch2 k); rwa [hp2] at this
  have haX := hsub a ha (hua.trans hk1)
  have hbX := hsub b hb (hub.trans hk2)
  have hnb : ¬ T.Under b (T.ch1 k) := fun h1 => not_under_both h hkn hkN h1 hub
  have hra := hc.2 a haX
  have hrb := hc.2 b hbX
  obtain ⟨ps, hps, hl⟩ := G.exists_walk_dist (c.len G) (hra.symm.trans hrb)
  obtain ⟨p, hp, u, v, hj, hu, hv⟩ := exists_cross hps hua hnb
  have hpm := hps.pair_lt hp
  have hω := cross_le h hG hpm hj hu hv (by omega)
  rw [hp1] at hω
  have hlen : c.len G p = G.pω p := by
    unfold len; rw [hhalf]; simp only [Finset.notMem_empty, ↓reduceIte]
    split_ifs <;> omega
  have h1 := PG.le_wlen (len := c.len G) hp
  have h2 := PG.dist_triangle (c.len G) hra.symm hrb
  rw [PG.dist_comm _ _ a c.x0] at h2
  have h3 := d_le_Δ (c := c) (G := G) haX
  have h4 := d_le_Δ (c := c) (G := G) hbX
  unfold d at h3 h4
  omega

/-- Lowering the threshold and undoing the halvings does not lower the radius. -/
theorem Δ_le_reset {r : Cl} (hr : r.Conn G) {x : ℕ} (hx : x ≤ r.θ) : r.Δ G ≤ (r.reset x).Δ G := by
  refine Finset.sup_le fun y hy => ?_
  have h1 : r.d G r.x0 y ≤ (r.reset x).d G (r.reset x).x0 y := by
    unfold d
    refine PG.dist_mono_len (fun p => ?_) (hr.2 y hy)
    unfold len reset
    simp only [Finset.notMem_empty, ↓reduceIte]
    split_ifs <;> omega
  exact h1.trans (d_le_Δ (c := r.reset x) (G := G) hy)

/-- **Replacing light pairs.** In a cluster that is a union of `θ`-nodes, with every `θ`-node of
weight at most `μ`, every cluster `c'` on the same vertices has distances at most
`2 d_r + |X| μ`. -/
theorem d_le_two_mw (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) (hGo : G.Ok)
    {r : Cl} (hr : r.Conn G) (hs : T.Sat G r.θ r.X) (hXn : r.X ⊆ Finset.range G.n)
    (hθ : 1 ≤ r.θ) {μ : ℕ} (hμ : ∀ a ∈ r.X, T.mw (T.top r.θ a) ≤ μ) {c' : Cl} (hX : c'.X = r.X)
    (hx : c'.x0 = r.x0) {y : ℕ} (hy : y ∈ r.X) :
    c'.d G c'.x0 y ≤ 2 * r.d G r.x0 y + r.X.card * μ := by
  have key : ∀ a b ps, G.IsWalk ↑r.X Set.univ a b ps → ∃ qs, G.IsWalk ↑r.X Set.univ a b qs ∧
      (∀ q ∈ qs, c'.len G q ≤ 2 * r.len G q + μ) ∧
      PG.wlen (fun q => 2 * r.len G q) qs ≤ PG.wlen (fun q => 2 * r.len G q) ps := by
    intro a b ps hw
    induction hw with
    | nil ha => exact ⟨[], .nil ha, by simp, le_rfl⟩
    | @cons a b' b'' p qs ha _ hj hrest ih =>
      obtain ⟨qs', hw', hb', hl'⟩ := ih
      by_cases hl : G.pω p < r.θ
      · obtain ⟨ws, hws⟩ := light_replace h hG hs hXn hθ hj hl ha hrest.start_mem
        refine ⟨ws ++ qs', (hws.mono le_rfl (Set.subset_univ _)).append hw', fun q hq => ?_, ?_⟩
        · rcases List.mem_append.mp hq with hq | hq
          · have := hws.pair_mem hq
            have := len_le (c := c') (G := G) q
            have := hμ a ha
            simp only [Set.mem_ofPred_eq] at *
            omega
          · exact hb' q hq
        · have h0 : PG.wlen (fun q => 2 * r.len G q) ws = 0 := by
            unfold PG.wlen
            refine List.sum_eq_zero fun z hz => ?_
            obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
            rw [len_eq_zero_of_light (hws.pair_mem hq).1]; rfl
          rw [PG.wlen_append, h0, PG.wlen_cons]
          omega
      · refine ⟨p :: qs', .cons ha (Set.mem_univ p) hj hw', fun q hq => ?_, ?_⟩
        · rcases List.mem_cons.mp hq with rfl | hq
          · have h1 := len_le (c := c') (G := G) q
            have h2 := half_le_len (c := r) (G := G) (p := q) (by omega)
            have he := PG.pω_even hGo q
            omega
          · exact hb' q hq
        · rw [PG.wlen_cons, PG.wlen_cons]
          omega
  obtain ⟨ps, hps, hl⟩ := G.exists_walk_dist (r.len G) (hr.2 y hy)
  obtain ⟨qs, hqs, hb, hle⟩ := key _ _ _ hps
  have := d_le_of_walk (c' := c') (f := fun q => 2 * r.len G q) (θ := μ) (a := c'.x0) (b := y)
    (ps := qs) (by rw [hX, hx]; exact hqs) hb
  simp only [PG.wlen_mul] at hle this
  rw [hX] at this
  unfold d at this ⊢
  rw [← hl]
  omega

theorem Δ_le_two_mw (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) (hGo : G.Ok)
    {r : Cl} (hr : r.Conn G) (hs : T.Sat G r.θ r.X) (hXn : r.X ⊆ Finset.range G.n)
    (hθ : 1 ≤ r.θ) {μ : ℕ} (hμ : ∀ a ∈ r.X, T.mw (T.top r.θ a) ≤ μ) (x : ℕ) :
    (r.reset x).Δ G ≤ 2 * r.Δ G + r.X.card * μ := by
  refine Finset.sup_le fun y hy => ?_
  have h1 := d_le_two_mw h hG hGo hr hs hXn hθ hμ (c' := r.reset x) rfl rfl hy
  have h2 := d_le_Δ (c := r) (G := G) hy
  show (r.reset x).d G (r.reset x).x0 y ≤ _
  omega

/-- **The reset threshold meets `Next`.** -/
theorem next_reset (h : T.Ok G) (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) (hGo : G.Ok)
    (hB : 1 ≤ P.B) {r : Cl} (hr : r.Good G) (hs : T.Sat G r.θ r.X)
    (hXn : r.X ⊆ Finset.range G.n) (hθ : 1 ≤ r.θ) (hX : 2 ≤ r.X.card)
    (hω : ∀ p < G.m, 8 * P.B * G.n ≤ G.pω p) (hlt : r.Δ G < P.B * r.X.card * r.θ) {μ : ℕ}
    (hμ : ∀ a ∈ r.X, T.mw (T.top r.θ a) ≤ μ)
    (hμ' : μ = 0 ∨ ∃ a ∈ r.X, T.mw (T.top r.θ a) = μ) :
    Next G P r (r.reset (thr (max (max (r.Δ G) μ) (4 * P.B * r.X.card)) P.B r.X.card)) := by
  set s := r.X.card with hsdef
  set S := max (max (r.Δ G) μ) (4 * P.B * s) with hS
  set x := thr S P.B s with hxdef
  have hsn : s ≤ G.n := by
    have := Finset.card_le_card hXn; rw [Finset.card_range] at this; exact this
  have h4 := θ_ge_four hB hr hX hsn hω hlt
  have hq : 0 < 4 * P.B * s := by positivity
  have hup : 4 * P.B * s * x ≤ S := thr_le (le_max_right _ _)
  have hlow : S < 8 * P.B * s * x := lt_thr hq
  have hx1 : 1 ≤ x := one_le_thr _ _ _
  have hμθ : μ < r.θ := by
    rcases hμ' with h0 | ⟨a, ha, he⟩
    · omega
    · rw [← he]
      exact (isTop_top h (Finset.mem_range.mp (hXn ha)) hθ).2.1
  -- the threshold drops by a factor four
  have h4x : 4 * x ≤ r.θ := by
    by_cases hm : max (r.Δ G) μ ≤ 4 * P.B * s
    · have e : S = 4 * P.B * s := by rw [hS]; exact max_eq_right hm
      rw [e] at hup
      have : x ≤ 1 := by
        by_contra hc
        have : 4 * P.B * s * 2 ≤ 4 * P.B * s * x := Nat.mul_le_mul_left _ (by omega)
        omega
      omega
    · push Not at hm
      have e : S = max (r.Δ G) μ := by rw [hS]; exact max_eq_left hm.le
      have h1 : S < P.B * s * r.θ := by
        rw [e]
        refine max_lt hlt ?_
        have : r.θ ≤ P.B * s * r.θ := Nat.le_mul_of_pos_left _ (by positivity)
        omega
      have e2 : 4 * P.B * s * x = P.B * s * (4 * x) := by ring
      rw [e2] at hup
      have := lt_of_le_of_lt hup h1
      exact (Nat.lt_of_mul_lt_mul_left this).le
  have hxθ : x ≤ r.θ := by omega
  -- the lower bound on the new radius
  have hbig : P.B * s * x ≤ (r.reset x).Δ G := by
    have e4 : 4 * P.B * s * x = 4 * (P.B * s * x) := by ring
    by_cases hm : max (r.Δ G) μ ≤ 4 * P.B * s
    · have e : S = 4 * P.B * s := by rw [hS]; exact max_eq_right hm
      have hx1' : x = 1 := by
        rw [e] at hup
        have : x ≤ 1 := by
          by_contra hc
          have : 4 * P.B * s * 2 ≤ 4 * P.B * s * x := Nat.mul_le_mul_left _ (by omega)
          omega
        omega
      rw [hx1']
      have h1 := Δ_one hr.conn hX hω (M := 8 * P.B * G.n) (by
        have : 0 < G.n := by omega
        have : 0 < 8 * P.B * G.n := by positivity
        omega)
      have : P.B * s ≤ P.B * G.n := Nat.mul_le_mul_left _ hsn
      have e8 : 8 * P.B * G.n = 8 * (P.B * G.n) := by ring
      rw [Nat.mul_one]
      omega
    · push Not at hm
      rcases le_total μ (r.Δ G) with hle | hle
      · have e : S = r.Δ G := by rw [hS, max_eq_left hm.le, max_eq_left hle]
        have := Δ_le_reset hr.conn hxθ
        omega
      · have e : S = μ := by rw [hS, max_eq_left hm.le, max_eq_right hle]
        rcases hμ' with h0 | ⟨a, ha, he⟩
        · omega
        have han : a < G.n := Finset.mem_range.mp (hXn ha)
        have hkN := top_lt_N h han hθ
        have hkn : G.n ≤ T.top r.θ a := by
          by_contra hc
          push Not at hc
          rw [h.leaf_mw _ hc] at he
          omega
        have hxμ : x ≤ μ := by
          have : x ≤ 4 * P.B * s * x := Nat.le_mul_of_pos_left _ hq
          omega
        have := mw_le_two_Δ h hG (c := r.reset x) hr.conn rfl hkn hkN
          (fun v hv hu => hs a ha v hv hu) (by rw [he]; exact hxμ)
        rw [he] at this
        omega
  -- the upper bound on the new radius
  have hsmall : (r.reset x).Δ G ≤ 32 * P.B * s ^ 2 * x := by
    have h1 := Δ_le_two_mw h hG hGo hr.conn hs hXn hθ hμ x
    rw [← hsdef] at h1
    have h2 : r.Δ G ≤ S := le_trans (le_max_left _ _) (le_max_left _ _)
    have h3 : μ ≤ S := le_trans (le_max_right _ _) (le_max_left _ _)
    have h5 : s * μ ≤ s * S := Nat.mul_le_mul_left _ h3
    have h6 : 2 * S ≤ s * S := Nat.mul_le_mul_right _ hX
    have h7 : 2 * s * S ≤ 2 * s * (8 * P.B * s * x) := Nat.mul_le_mul_left _ hlow.le
    have e : 2 * s * (8 * P.B * s * x) = 16 * P.B * s ^ 2 * x := by ring
    have e' : 2 * s * S = s * S + s * S := by ring
    have e2 : 32 * P.B * s ^ 2 * x = 2 * (16 * P.B * s ^ 2 * x) := by ring
    omega
  exact Or.inr ⟨hlt, rfl, rfl, rfl, rfl, rfl, h4x, hx1, Or.inr hbig, hsmall⟩

end Cl

open KT in
/-- **The first cluster.** With at least two vertices, the root threshold
`thr (max μ (4 B n)) B n` for the weight `μ` of the root of the Kruskal tree meets the invariant. -/
theorem root_inv {T : KT} {G : PG} {P : Par} (h : T.Ok G)
    (hG : ∀ p < G.m, G.pu p < G.n ∧ G.pv p < G.n) (hB : 1 ≤ P.B)
    (hω : ∀ p < G.m, 8 * P.B * G.n ≤ G.pω p) (hc : (root G 1).Conn G) (hn : 2 ≤ G.n) :
    (root G (thr (max (T.mw (T.N - 1)) (4 * P.B * G.n)) P.B G.n)).Inv G P := by
  set μ := T.mw (T.N - 1) with hμ
  set S := max μ (4 * P.B * G.n) with hS
  set x := thr S P.B G.n with hxdef
  have hN := h.n_lt
  have hq : 0 < 4 * P.B * G.n := by positivity
  have hup : 4 * P.B * G.n * x ≤ S := thr_le (le_max_right _ _)
  have hlow : S < 8 * P.B * G.n * x := lt_thr hq
  have hcard : (root G x).X.card = G.n := by simp [root]
  have hcx : (root G x).Conn G := hc
  have hgood : (root G x).Good G :=
    ⟨hcx, ⟨.nil (by simpa [root] using hc.1), fun i hi => absurd hi (by simp [root])⟩,
      fun p hp => absurd hp (by simp [root])⟩
  refine ⟨hgood, one_le_thr _ _ _, Or.inr ?_, ?_, fun _ h => h⟩
  · show P.B * (root G x).X.card * x ≤ _
    rw [hcard]
    have e4 : 4 * P.B * G.n * x = 4 * (P.B * G.n * x) := by ring
    by_cases hm : μ ≤ 4 * P.B * G.n
    · have e : S = 4 * P.B * G.n := by rw [hS]; exact max_eq_right hm
      have hx1 : x = 1 := by
        rw [e] at hup
        have : x ≤ 1 := by
          by_contra hc'
          have : 4 * P.B * G.n * 2 ≤ 4 * P.B * G.n * x := Nat.mul_le_mul_left _ (by omega)
          omega
        have := one_le_thr S P.B G.n
        omega
      rw [hx1]
      have h1 := Cl.Δ_one (r := root G 1) hc (by simp [root]; omega) hω (M := 8 * P.B * G.n)
        (by have : 0 < 8 * P.B * G.n := by positivity
            omega)
      rw [root_eq_reset] at h1
      have e8 : 8 * P.B * G.n = 8 * (P.B * G.n) := by ring
      show P.B * G.n * 1 ≤ _
      rw [Nat.mul_one]
      omega
    · push Not at hm
      have e : S = μ := by rw [hS]; exact max_eq_left hm.le
      have hxμ : x ≤ μ := by
        have : x ≤ 4 * P.B * G.n * x := Nat.le_mul_of_pos_left _ hq
        omega
      have := Cl.mw_le_two_Δ h hG (c := root G x) hcx rfl (k := T.N - 1) (by omega) (by omega)
        (fun v hv _ => by simpa [root] using hv) hxμ
      rw [← hμ] at this
      omega
  · show _ ≤ 32 * P.B * G.n ^ 2 * x
    have hd : ∀ y ∈ (root G x).X, (root G x).d G (root G x).x0 y ≤ G.n * μ := by
      intro y hy
      have hyn : y < G.n := by simpa [root] using hy
      obtain ⟨ps, hps⟩ := walk_of_under h hG (T.N - 1) (by omega) 0 y (by omega) hyn
        (h.all 0 (by omega)) (h.all y hyn)
      have := Cl.d_le_of_walk (c' := root G x) (f := fun _ => 0) (θ := μ) (ps := ps)
        (hps.mono (fun v hv => by simpa [root] using hv.1) (Set.subset_univ _)) (fun q hq => by
          have := Cl.len_le (c := root G x) (G := G) q
          have := hps.pair_mem hq
          simp only [Set.mem_ofPred_eq] at this
          omega)
      have e : PG.wlen (fun _ => 0) ps = 0 := by
        unfold PG.wlen; simp
      rw [e, hcard] at this
      simpa [root] using this
    have h1 : (root G x).Δ G ≤ G.n * μ := Finset.sup_le hd
    have h2 : μ ≤ S := le_max_left _ _
    have h3 : G.n * μ ≤ G.n * S := Nat.mul_le_mul_left _ h2
    have h4 : G.n * S ≤ G.n * (8 * P.B * G.n * x) := Nat.mul_le_mul_left _ hlow.le
    have e : G.n * (8 * P.B * G.n * x) = 8 * P.B * G.n ^ 2 * x := by ring
    have e2 : 32 * P.B * G.n ^ 2 * x = 4 * (8 * P.B * G.n ^ 2 * x) := by ring
    omega

end MinCostFlow.LowStretch
