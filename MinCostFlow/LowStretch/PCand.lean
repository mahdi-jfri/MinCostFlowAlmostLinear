module

public import MinCostFlow.LowStretch.Grow

/-!
# The candidate radii of the petal search

The search cannot try every radius. Between two keys of the queue the petal does not change, so
the program tries, for each interval `[a, k - 1]` of radii with the same petal and each bucket
`q` that meets it, only the radius `min(k - 1, b_q)` with bucket `q` (here `b_q = lo + q bw` is the
right end of bucket `q`). This file shows that this is enough.

`Fail a` says that no pair `(r, q)` with `r < a` in bucket `q` has the first test at `r` and the
volume test at the right end of `q`. A failed interval extends `Fail` (`Fail.step`). If `Fail`
held past the last bucket, `exists_radius_end` would be contradicted (`Fail.false`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

variable {G : PG} {P : Par}

namespace Cl

variable {c : Cl}

/-- No radius below `a` passes the first test in a bucket whose right end passes the volume test. -/
def Fail (G : PG) (P : Par) (c : Cl) (Y : Finset ℕ) (pd : PD) (lo a : ℕ) : Prop :=
  ∀ r q, r < a → 1 ≤ q → q ≤ P.L → lo + (q - 1) * c.bw G P ≤ r → r ≤ lo + q * c.bw G P →
    ¬ (c.cost G P Y (pd.withR r) * c.sq G P q ≤ 8 * c.vol G P Y (pd.withR r) ∧
      c.vol G P Y (pd.withR (lo + q * c.bw G P)) ≤ c.T G P q)

theorem fail_zero (Y : Finset ℕ) (pd : PD) (lo : ℕ) : Fail G P c Y pd lo 0 :=
  fun _ _ h => absurd h (Nat.not_lt_zero _)

/-- **One interval.** If the petal is the same for all radii in `[a, k - 1]`, and for every
bucket `q` that meets this interval the radius `min(k - 1, b_q)` fails one of the two tests of
`q`, then `Fail` extends from `a` to `k`. -/
theorem Fail.step (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) {pd : PD}
    {lo a k : ℕ} (hf : Fail G P c Y pd lo a)
    (hsame : ∀ r, a ≤ r → r < k → c.carve G Y (pd.withR r) = c.carve G Y (pd.withR (k - 1)))
    (htest : ∀ q, 1 ≤ q → q ≤ P.L → lo + (q - 1) * c.bw G P < k → a ≤ lo + q * c.bw G P →
      ¬ (c.cost G P Y (pd.withR (min (k - 1) (lo + q * c.bw G P))) * c.sq G P q ≤
          8 * c.vol G P Y (pd.withR (min (k - 1) (lo + q * c.bw G P))) ∧
        c.vol G P Y (pd.withR (min (k - 1) (lo + q * c.bw G P))) ≤ c.T G P q)) :
    Fail G P c Y pd lo k := by
  intro r q hr hq1 hqL h1 h2 ⟨t1, t2⟩
  by_cases hra : r < a
  · exact hf r q hra hq1 hqL h1 h2 ⟨t1, t2⟩
  push Not at hra
  set r' := min (k - 1) (lo + q * c.bw G P) with hr'
  have hrr : r ≤ r' := le_min (by omega) h2
  have hr'k : r' < k := by omega
  have hc1 : c.carve G Y (pd.withR r) = c.carve G Y (pd.withR r') := by
    rw [hsame r hra hr, hsame r' (by omega) hr'k]
  have hcost : c.cost G P Y (pd.withR r') = c.cost G P Y (pd.withR r) := by
    unfold cost; rw [hc1]
  refine htest q hq1 hqL (by omega) (by omega) ⟨?_, ?_⟩
  · rw [hcost]
    exact t1.trans (by linarith [vol_mono (P := P) hGo hc hY pd hrr])
  · exact (vol_mono (P := P) hGo hc hY pd (min_le_right _ _)).trans t2

/-- **The search finds a radius.** `Fail` cannot hold past the last bucket. -/
theorem Fail.false (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) {pd : PD}
    {lo a : ℕ} (hf : Fail G P c Y pd lo a) (ha : lo + P.L * c.bw G P < a) (hκ : 1 ≤ P.κ)
    (hL : 1 ≤ P.L) (hΔ : 8 * P.L * (lam P 0 + 3) ≤ c.Δ G) (hV : c.V G P ≤ 2 ^ lam P 0 * P.κ) :
    False := by
  obtain ⟨r, q, h1, h2, h3, h4, h5, h6⟩ := exists_radius_end hGo hc hY pd lo hκ hL hΔ hV
  have : q * c.bw G P ≤ P.L * c.bw G P := Nat.mul_le_mul_right _ h2
  exact hf r q (by omega) h1 h2 h3 h4 ⟨h5, h6⟩

/-! ### One bucket at a time

The program handles the buckets one by one, so it keeps the per-bucket form `BFail`. -/

/-- No radius below `x` in bucket `q` passes the first test while the right end of `q` passes
the volume test. -/
def BFail (G : PG) (P : Par) (c : Cl) (Y : Finset ℕ) (pd : PD) (lo q x : ℕ) : Prop :=
  ∀ r, r < x → lo + (q - 1) * c.bw G P ≤ r → r ≤ lo + q * c.bw G P →
    ¬ (c.cost G P Y (pd.withR r) * c.sq G P q ≤ 8 * c.vol G P Y (pd.withR r) ∧
      c.vol G P Y (pd.withR (lo + q * c.bw G P)) ≤ c.T G P q)

theorem bfail_of_le {Y : Finset ℕ} {pd : PD} {lo q x : ℕ} (h : x ≤ lo + (q - 1) * c.bw G P) :
    BFail G P c Y pd lo q x :=
  fun r hr h1 _ => absurd h1 (by omega)

theorem BFail.mono {Y : Finset ℕ} {pd : PD} {lo q x y : ℕ} (hf : BFail G P c Y pd lo q y)
    (h : x ≤ y) : BFail G P c Y pd lo q x :=
  fun r hr => hf r (by omega)

/-- A bucket that ends below `x` and fails below `x` fails everywhere. -/
theorem BFail.all {Y : Finset ℕ} {pd : PD} {lo q x : ℕ} (hf : BFail G P c Y pd lo q x)
    (h : lo + q * c.bw G P < x) (y : ℕ) : BFail G P c Y pd lo q y :=
  fun r _ h1 h2 => hf r (by omega) h1 h2

theorem fail_of_bfail {Y : Finset ℕ} {pd : PD} {lo x : ℕ}
    (h : ∀ q, 1 ≤ q → q ≤ P.L → BFail G P c Y pd lo q x) : Fail G P c Y pd lo x :=
  fun r q hr hq1 hqL h1 h2 => h q hq1 hqL r hr h1 h2

/-- **One interval, one bucket.** As `Fail.step`, for bucket `q` alone. -/
theorem BFail.step (hGo : G.Ok) (hc : c.Conn G) {Y : Finset ℕ} (hY : Y ⊆ c.X) {pd : PD}
    {lo q a k : ℕ} (hf : BFail G P c Y pd lo q a)
    (hsame : ∀ r, a ≤ r → r < k → c.carve G Y (pd.withR r) = c.carve G Y (pd.withR (k - 1)))
    (htest : lo + (q - 1) * c.bw G P < k → a ≤ lo + q * c.bw G P →
      ¬ (c.cost G P Y (pd.withR (min (k - 1) (lo + q * c.bw G P))) * c.sq G P q ≤
          8 * c.vol G P Y (pd.withR (min (k - 1) (lo + q * c.bw G P))) ∧
        c.vol G P Y (pd.withR (min (k - 1) (lo + q * c.bw G P))) ≤ c.T G P q)) :
    BFail G P c Y pd lo q k := by
  intro r hr h1 h2 ⟨t1, t2⟩
  by_cases hra : r < a
  · exact hf r hra h1 h2 ⟨t1, t2⟩
  push Not at hra
  set r' := min (k - 1) (lo + q * c.bw G P) with hr'
  have hrr : r ≤ r' := le_min (by omega) h2
  have hr'k : r' < k := by omega
  have hc1 : c.carve G Y (pd.withR r) = c.carve G Y (pd.withR r') := by
    rw [hsame r hra hr, hsame r' (by omega) hr'k]
  have hcost : c.cost G P Y (pd.withR r') = c.cost G P Y (pd.withR r) := by
    unfold cost; rw [hc1]
  refine htest (by omega) (by omega) ⟨?_, ?_⟩
  · rw [hcost]
    exact t1.trans (by linarith [vol_mono (P := P) hGo hc hY pd hrr])
  · exact (vol_mono (P := P) hGo hc hY pd (min_le_right _ _)).trans t2

end Cl

end MinCostFlow.LowStretch
