module

public import MinCostFlow.LowStretch.Stretch2

/-!
# Region growing finds a radius

This file shows that the tests of region growing can always be met. When the radius grows by
`1`, the volume grows by at least `cost / 8` (`vol_succ`): every active pair that leaves the petal
adds `cw / (8 ω)`, whether it still leaves or is now inside. So if the test
`cost · s ≤ 8 · vol` failed at every radius of a range of width `w ≥ (λ + 3) s`, the volume would
grow by a factor `2^(λ + 3)` across the range. We pick the first bucket `q` whose right end passes
the volume test `vol ≤ T_q`. The left end then fails the test of bucket `q - 1` (or is at least
`κ` when `q = 1`), and the growth would make the volume larger than `V`, which is impossible.
So some radius of bucket `q` passes both tests (`exists_radius`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open Real

variable {G : PG} {P : Par}

/-- The petal `pd` with radius `r`. -/
def PD.withR (pd : PD) (r : ℕ) : PD := { pd with r := r }

@[simp] theorem PD.withR_tj (pd : PD) (r : ℕ) : (pd.withR r).tj = pd.tj := rfl
@[simp] theorem PD.withR_hw (pd : PD) (r : ℕ) : (pd.withR r).hw = pd.hw := rfl
@[simp] theorem PD.withR_r (pd : PD) (r : ℕ) : (pd.withR r).r = r := rfl
@[simp] theorem PD.withR_i (pd : PD) (r : ℕ) : (pd.withR r).i = pd.i := rfl

namespace Cl

variable {c : Cl}

theorem carve_mono {Y : Finset ℕ} {pd : PD} {r r' : ℕ} (h : r ≤ r') :
    c.carve G Y (pd.withR r) ⊆ c.carve G Y (pd.withR r') := fun v hv => by
  obtain ⟨h1, h2⟩ := mem_carve.mp hv
  exact mem_carve.mpr ⟨h1, Petal.mono h h2⟩

theorem ent_withR (Y : Finset ℕ) (pd : PD) (r : ℕ) (v : ℕ) :
    c.ent G Y (pd.withR r) v = c.ent G Y pd v := rfl

theorem aux_add {cw ω x : ℝ} (hω : 0 < ω) :
    cw * x / (8 * ω) + cw / ω / 8 = cw * (x + 1) / (8 * ω) := by
  field_simp

theorem aux_le {cw ω x : ℝ} (hcw : 0 ≤ cw) (hω : 0 < ω) (hx : x + 1 ≤ 8 * ω) :
    cw * (x + 1) / (8 * ω) ≤ cw := by
  rw [div_le_iff₀ (by positivity)]; nlinarith

open Classical in
/-- One more unit of radius adds at least `cw / (8 ω)` for a leaving active pair. -/
theorem contrib_succ (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) (pd : PD)
    (r : ℕ) {p : ℕ} (hp : p ∈ c.act G P) :
    c.contrib G P Y (pd.withR r) p +
        (if Leaves G Y (c.carve G Y (pd.withR r)) p then (P.cw p : ℝ) / G.pω p / 8 else 0) ≤
      c.contrib G P Y (pd.withR (r + 1)) p := by
  have hsub : c.carve G Y (pd.withR r) ⊆ c.carve G Y (pd.withR (r + 1)) :=
    carve_mono (Nat.le_succ r)
  have hω : (0 : ℝ) < G.pω p := by exact_mod_cast (hGo p (mem_act.mp hp).1).2.2.2.2
  have hcw : (0 : ℝ) ≤ P.cw p := by positivity
  by_cases h1 : Inside G (c.carve G Y (pd.withR r)) p
  · have h1' : Inside G (c.carve G Y (pd.withR (r + 1))) p := ⟨hsub h1.1, hsub h1.2⟩
    have hnl : ¬ Leaves G Y (c.carve G Y (pd.withR r)) p := by
      rintro (⟨-, h⟩ | ⟨-, h⟩)
      · exact (Finset.mem_sdiff.mp h).2 h1.2
      · exact (Finset.mem_sdiff.mp h).2 h1.1
    simp only [contrib, h1, h1', hnl, ↓reduceIte, add_zero, le_refl]
  by_cases h2 : Leaves G Y (c.carve G Y (pd.withR r)) p
  · have hlt := leaves_lt hc hY hp h2
    simp only [contrib, h1, h2, ↓reduceIte]
    rcases h2 with ⟨hu, hv⟩ | ⟨hv, hu⟩
    · have he : inEnd G (c.carve G Y (pd.withR r)) p = G.pu p := by simp [inEnd, hu]
      have he' : inEnd G (c.carve G Y (pd.withR (r + 1))) p = G.pu p := by simp [inEnd, hsub hu]
      rw [he] at hlt ⊢
      have hle := (ent_spec hu).2
      simp only [PD.withR_r] at hle hlt ⊢
      rw [ent_withR] at hle hlt ⊢
      have hc1 : ((r - c.ent G Y pd (G.pu p) : ℕ) : ℝ) = r - c.ent G Y pd (G.pu p) := by
        rw [Nat.cast_sub hle]
      rw [hc1, aux_add hω]
      by_cases h3 : G.pv p ∈ c.carve G Y (pd.withR (r + 1))
      · have hin : Inside G (c.carve G Y (pd.withR (r + 1))) p := ⟨hsub hu, h3⟩
        simp only [hin, ↓reduceIte]
        refine aux_le hcw hω ?_
        have : (r : ℝ) < c.ent G Y pd (G.pu p) + 8 * G.pω p := by exact_mod_cast hlt
        have h4 : (r : ℝ) + 1 ≤ c.ent G Y pd (G.pu p) + 8 * G.pω p := by
          have : r + 1 ≤ c.ent G Y pd (G.pu p) + 8 * G.pω p := hlt
          exact_mod_cast this
        linarith
      · have hnin : ¬ Inside G (c.carve G Y (pd.withR (r + 1))) p := fun h => h3 h.2
        have hl' : Leaves G Y (c.carve G Y (pd.withR (r + 1))) p :=
          Or.inl ⟨hsub hu, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hv).1, h3⟩⟩
        simp only [hnin, hl', ↓reduceIte, he', PD.withR_r, ent_withR]
        rw [Nat.cast_sub (by omega)]
        push_cast
        apply le_of_eq; ring_nf
    · have hu' : G.pu p ∉ c.carve G Y (pd.withR r) := (Finset.mem_sdiff.mp hu).2
      have he : inEnd G (c.carve G Y (pd.withR r)) p = G.pv p := by simp [inEnd, hu']
      rw [he] at hlt ⊢
      have hle := (ent_spec hv).2
      simp only [PD.withR_r] at hle hlt ⊢
      rw [ent_withR] at hle hlt ⊢
      have hc1 : ((r - c.ent G Y pd (G.pv p) : ℕ) : ℝ) = r - c.ent G Y pd (G.pv p) := by
        rw [Nat.cast_sub hle]
      rw [hc1, aux_add hω]
      by_cases h3 : G.pu p ∈ c.carve G Y (pd.withR (r + 1))
      · have hin : Inside G (c.carve G Y (pd.withR (r + 1))) p := ⟨h3, hsub hv⟩
        simp only [hin, ↓reduceIte]
        refine aux_le hcw hω ?_
        have h4 : (r : ℝ) + 1 ≤ c.ent G Y pd (G.pv p) + 8 * G.pω p := by
          have : r + 1 ≤ c.ent G Y pd (G.pv p) + 8 * G.pω p := hlt
          exact_mod_cast this
        linarith
      · have hnin : ¬ Inside G (c.carve G Y (pd.withR (r + 1))) p := fun h => h3 h.1
        have hl' : Leaves G Y (c.carve G Y (pd.withR (r + 1))) p :=
          Or.inr ⟨hsub hv, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hu).1, h3⟩⟩
        have he' : inEnd G (c.carve G Y (pd.withR (r + 1))) p = G.pv p := by simp [inEnd, h3]
        simp only [hnin, hl', ↓reduceIte, he', PD.withR_r, ent_withR]
        rw [Nat.cast_sub (by omega)]
        push_cast
        apply le_of_eq; ring_nf
  · simp only [h2, ↓reduceIte, add_zero]
    have h0 : c.contrib G P Y (pd.withR r) p = 0 := by simp [contrib, h1, h2]
    rw [h0]
    exact contrib_nonneg _ _ _

/-- One more unit of radius adds at least `cost / 8` to the volume. -/
theorem vol_succ (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) (pd : PD) (r : ℕ) :
    c.vol G P Y (pd.withR r) + c.cost G P Y (pd.withR r) / 8 ≤ c.vol G P Y (pd.withR (r + 1)) := by
  classical
  rw [vol_eq, vol_eq]
  unfold cost
  simp only
  rw [Finset.sum_filter, Finset.sum_div, add_assoc, ← Finset.sum_add_distrib]
  refine add_le_add le_rfl (Finset.sum_le_sum fun p hp => ?_)
  have := contrib_succ (P := P) hGo hc hY pd r hp
  split_ifs at this ⊢ with h
  · exact this
  · simpa using this

theorem vol_mono (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) (pd : PD) {r r' : ℕ}
    (h : r ≤ r') : c.vol G P Y (pd.withR r) ≤ c.vol G P Y (pd.withR r') := by
  induction r', h using Nat.le_induction with
  | base => exact le_rfl
  | succ r' _ ih =>
    have := vol_succ (P := P) hGo hc hY pd r'
    have := cost_nonneg (c := c) (G := G) (P := P) Y (pd.withR r')
    linarith

theorem vol_le_V (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) (pd : PD) :
    c.vol G P Y pd ≤ c.V G P := by
  rw [vol_eq]
  unfold V
  have := Finset.sum_le_sum fun p (hp : p ∈ c.act G P) => contrib_le (P := P) hGo hc hY pd hp
  linarith

end Cl

/-- Repeated growth by a factor `1 + 1/s`. -/
theorem growth {f : ℕ → ℝ} {a w s : ℕ} (hf : 0 ≤ f a)
    (h : ∀ j < w, f (a + j) * (1 + 1 / (s : ℝ)) ≤ f (a + j + 1)) :
    f a * (1 + 1 / (s : ℝ)) ^ w ≤ f (a + w) := by
  induction w with
  | zero => simp
  | succ w ih =>
    have h1 := ih fun j hj => h j (by omega)
    have h2 := h w (by omega)
    have hpos : (0 : ℝ) ≤ 1 + 1 / (s : ℝ) := by positivity
    calc f a * (1 + 1 / (s : ℝ)) ^ (w + 1) = (f a * (1 + 1 / (s : ℝ)) ^ w) * (1 + 1 / (s : ℝ)) := by
          ring
      _ ≤ f (a + w) * (1 + 1 / (s : ℝ)) := mul_le_mul_of_nonneg_right h1 hpos
      _ ≤ f (a + w + 1) := h2
      _ = f (a + (w + 1)) := by rw [Nat.add_assoc]

theorem two_pow_le {s w lam : ℕ} (hs : 1 ≤ s) (hw : (lam + 3) * s ≤ w) :
    (2 : ℝ) ^ (lam + 3) ≤ (1 + 1 / (s : ℝ)) ^ w := by
  have hsr : (1 : ℝ) ≤ s := by exact_mod_cast hs
  have h1 : (2 : ℝ) ≤ (1 + 1 / (s : ℝ)) ^ s := by
    have := one_add_mul_le_pow (show (-2 : ℝ) ≤ 1 / s by
      have : (0 : ℝ) ≤ 1 / s := by positivity
      linarith) s
    have e : (s : ℝ) * (1 / s) = 1 := by field_simp
    linarith
  have hb : (1 : ℝ) ≤ 1 + 1 / (s : ℝ) := by
    have : (0 : ℝ) ≤ 1 / s := by positivity
    linarith
  calc (2 : ℝ) ^ (lam + 3) ≤ ((1 + 1 / (s : ℝ)) ^ s) ^ (lam + 3) :=
        pow_le_pow_left₀ (by norm_num) h1 _
    _ = (1 + 1 / (s : ℝ)) ^ ((lam + 3) * s) := by rw [← pow_mul, mul_comm]
    _ ≤ (1 + 1 / (s : ℝ)) ^ w := pow_le_pow_right₀ hb hw

namespace Cl

variable {c : Cl}

/-- **Region growing, with the bucket end.** Some radius in some bucket `q` passes the first
test, and the right end of bucket `q` passes the volume test of `q`. -/
theorem exists_radius_end (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) (pd : PD)
    (lo : ℕ) (hκ : 1 ≤ P.κ) (hL : 1 ≤ P.L) (hΔ : 8 * P.L * (lam P 0 + 3) ≤ c.Δ G)
    (hV : c.V G P ≤ 2 ^ lam P 0 * P.κ) :
    ∃ r q, 1 ≤ q ∧ q ≤ P.L ∧ lo + (q - 1) * c.bw G P ≤ r ∧ r ≤ lo + q * c.bw G P ∧
      c.cost G P Y (pd.withR r) * c.sq G P q ≤ 8 * c.vol G P Y (pd.withR r) ∧
      c.vol G P Y (pd.withR (lo + q * c.bw G P)) ≤ c.T G P q := by
  classical
  set v : ℕ → ℝ := fun r => c.vol G P Y (pd.withR r) with hv
  have hκr : (0 : ℝ) < P.κ := by exact_mod_cast hκ
  have hVpos : (0 : ℝ) < c.V G P := lt_of_lt_of_le hκr V_ge
  have hvV : ∀ r, v r ≤ c.V G P := fun r => vol_le_V hGo hc hY _
  have hex : ∃ q, 1 ≤ q ∧ q ≤ P.L ∧ v (lo + q * c.bw G P) ≤ c.T G P q := by
    refine ⟨P.L, hL, le_rfl, ?_⟩
    unfold T
    have e : lam P P.L = 1 := by unfold lam; simp
    rw [e]
    have := hvV (lo + P.L * c.bw G P)
    have : (0 : ℝ) ≤ P.κ := hκr.le
    norm_num
    linarith
  obtain ⟨hq1, hqL, hqT⟩ := Nat.find_spec hex
  set q := Nat.find hex with hq
  set a := lo + (q - 1) * c.bw G P with ha
  have hb : lo + q * c.bw G P = a + c.bw G P := by
    rw [ha, Nat.add_assoc, ← Nat.succ_mul, Nat.succ_eq_add_one, Nat.sub_add_cancel hq1]
  by_cases hgood : ∃ r, a ≤ r ∧ r ≤ lo + q * c.bw G P ∧
      c.cost G P Y (pd.withR r) * c.sq G P q ≤ 8 * c.vol G P Y (pd.withR r)
  · obtain ⟨r, h1, h2, h3⟩ := hgood
    exact ⟨r, q, hq1, hqL, h1, h2, h3, hqT⟩
  exfalso
  push Not at hgood
  -- the slack and the bucket width
  have hbw : lam P 0 + 3 ≤ c.bw G P := by
    unfold bw
    rw [Nat.le_div_iff_mul_le (by omega), Nat.le_div_iff_mul_le (by norm_num)]
    have : (lam P 0 + 3) * P.L * 8 = 8 * P.L * (lam P 0 + 3) := by ring
    omega
  have hlq := lam_le (P := P) (q - 1)
  have hs : 1 ≤ c.sq G P q := by
    unfold sq
    rw [Nat.le_div_iff_mul_le (by omega)]
    omega
  have hsw : (lam P (q - 1) + 3) * c.sq G P q ≤ c.bw G P := by
    unfold sq
    rw [mul_comm]
    exact Nat.div_mul_le_self _ _
  -- the volume grows by `1 + 1/s` at each step of the bucket
  have hstep : ∀ j < c.bw G P, v (a + j) * (1 + 1 / (c.sq G P q : ℝ)) ≤ v (a + j + 1) := by
    intro j hj
    have h1 := vol_succ (P := P) hGo hc hY pd (a + j)
    have h2 := hgood (a + j) (by omega) (by omega)
    have hsr : (0 : ℝ) < c.sq G P q := by exact_mod_cast hs
    have h3 : v (a + j) / c.sq G P q ≤ c.cost G P Y (pd.withR (a + j)) / 8 := by
      rw [div_le_div_iff₀ hsr (by norm_num)]
      simp only [hv]
      linarith
    have e : v (a + j) * (1 + 1 / (c.sq G P q : ℝ)) = v (a + j) + v (a + j) / c.sq G P q := by
      field_simp
    rw [e]
    simp only [hv] at h3 ⊢
    linarith
  have hva : (0 : ℝ) ≤ v a := le_trans hκr.le (vol_ge _ _)
  have hg := growth hva hstep
  rw [← hb] at hg
  have hp2 := two_pow_le hs hsw
  have hg2 : v a * 2 ^ (lam P (q - 1) + 3) ≤ v (lo + q * c.bw G P) :=
    le_trans (mul_le_mul_of_nonneg_left hp2 hva) hg
  have hvb := hvV (lo + q * c.bw G P)
  have hp : (0 : ℝ) < 2 ^ lam P (q - 1) := by positivity
  have e8 : (2 : ℝ) ^ (lam P (q - 1) + 3) = 8 * 2 ^ lam P (q - 1) := by rw [pow_add]; norm_num; ring
  rw [e8] at hg2
  by_cases hq1' : q = 1
  · -- the first bucket: the volume starts at `κ`
    have hva' : (P.κ : ℝ) ≤ v a := vol_ge _ _
    rw [show q - 1 = 0 by omega] at hg2
    have : (P.κ : ℝ) * (8 * 2 ^ lam P 0) ≤ v a * (8 * 2 ^ lam P 0) :=
      mul_le_mul_of_nonneg_right hva' (by positivity)
    nlinarith
  · -- a later bucket: the left end failed the volume test of the bucket before
    have hmin := Nat.find_min hex (show q - 1 < q by omega)
    push Not at hmin
    have hfail := hmin (by omega) (by omega)
    have e : lo + (q - 1) * c.bw G P = a := rfl
    rw [e] at hfail
    unfold T at hfail
    have h4 : 4 * c.V G P < v a * 2 ^ lam P (q - 1) := by
      have : 4 * c.V G P / 2 ^ lam P (q - 1) < v a := by linarith
      rwa [div_lt_iff₀ hp] at this
    nlinarith

/-- **Region growing.** Some radius in some bucket passes both tests. -/
theorem exists_radius (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) (pd : PD)
    (lo : ℕ) (hκ : 1 ≤ P.κ) (hL : 1 ≤ P.L) (hΔ : 8 * P.L * (lam P 0 + 3) ≤ c.Δ G)
    (hV : c.V G P ≤ 2 ^ lam P 0 * P.κ) :
    ∃ r q, 1 ≤ q ∧ q ≤ P.L ∧ lo + (q - 1) * c.bw G P ≤ r ∧ r ≤ lo + q * c.bw G P ∧
      c.cost G P Y (pd.withR r) * c.sq G P q ≤ 8 * c.vol G P Y (pd.withR r) ∧
      c.vol G P Y (pd.withR r) ≤ c.T G P q := by
  obtain ⟨r, q, h1, h2, h3, h4, h5, h6⟩ := exists_radius_end hGo hc hY pd lo hκ hL hΔ hV
  exact ⟨r, q, h1, h2, h3, h4, h5, (vol_mono hGo hc hY pd h4).trans h6⟩

end Cl

end MinCostFlow.LowStretch
