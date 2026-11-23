module

public import MinCostFlow.LowStretch.ProgClusterSetupCh

/-!
# The setup of a cluster: the word bounds of the chain

The calls after `pgP` ask a few word bounds (`SuWords`). They follow from `ClPre.room_sq`, whose
term `2^(2J + 20) (N + m + 2)² (Mw + 2)²` is at least `2^20 (2^J Z)²` with `Z = (N + m + 2)(Mw + 2)`
(`ClPre.room_core`). Here `Z` is at least `θ`, `INF / 4` and `n + 2`, and `2^J > (n + 2)²`.
The largest bound is `2^2^L ≤ 256 (n + 2)⁴` (`two_pow_two_pow_pL_le`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ}

/-- `2^2^(pL n) ≤ 256 (n + 2)⁴`, since `2^(pL n) ≤ 4 pa n + 4` and `2^(pa n) ≤ 2 (n + 2)`. -/
theorem two_pow_two_pow_pL_le (n : ℕ) : 2 ^ 2 ^ pL n ≤ 256 * (n + 2) ^ 4 := by
  have h1 := two_pow_pL_le n
  have h2 : 2 ^ pa n ≤ 2 * (n + 2) := by
    unfold pa
    rw [pow_succ, mul_comm]
    exact Nat.mul_le_mul_left _ (Nat.pow_log_le_self 2 (by omega))
  calc 2 ^ 2 ^ pL n ≤ 2 ^ (4 * pa n + 4) := Nat.pow_le_pow_right (by norm_num) h1
    _ = 16 * (2 ^ pa n) ^ 4 := by rw [pow_add, pow_mul', mul_comm]; norm_num
    _ ≤ 16 * (2 * (n + 2)) ^ 4 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2 4)
    _ = 256 * (n + 2) ^ 4 := by ring

/-- **The core of the room**: with `Z = (N + m + 2)(Mw + 2)`, which is at least `θ`, `INF / 4`
and `n + 2`, `h + 2^20 (2^J Z)² < 2^w`. -/
theorem ClPre.room_core (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    ∃ Z, 1 ≤ Z ∧ c.θ ≤ Z ∧ (GlobL.read mem GB).INF ≤ 4 * Z ∧ G.n + 2 ≤ Z ∧
      h + 2 ^ 20 * ((2 ^ (GlobL.read mem GB).J * Z) * (2 ^ (GlobL.read mem GB).J * Z)) <
        2 ^ w := by
  obtain ⟨Mw, hM, hINF, hroom⟩ := hp.room_sq
  set J := (GlobL.read mem GB).J
  have hcard : c.X.card ≤ G.n := by
    have := Finset.card_le_card hp.ok.inv.sub
    simpa using this
  have hΔ : c.Δ G ≤ G.n * Mw :=
    (Cl.Δ_le_card_mul hp.ok.inv.good.conn hM).trans (Nat.mul_le_mul_right _ hcard)
  have hθΔ : c.θ ≤ c.Δ G := by
    have hB : 1 ≤ P.B := hp.ok.hB
    rcases hp.ok.inv.big with h' | h'
    · omega
    · have : 1 * 1 * c.θ ≤ P.B * c.X.card * c.θ :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul hB (by omega))
      omega
  have hN := hp.ok.tree.n_lt
  refine ⟨(T.N + G.m + 2) * (Mw + 2), ?_, ?_, ?_, ?_, ?_⟩
  · exact Nat.one_le_iff_ne_zero.mpr (by positivity)
  · have : (G.n + 2) * (Mw + 2) ≤ (T.N + G.m + 2) * (Mw + 2) :=
      Nat.mul_le_mul (by omega) le_rfl
    have e : (G.n + 2) * (Mw + 2) = G.n * Mw + 2 * G.n + 2 * Mw + 4 := by ring
    omega
  · have : (G.n + 2) * (Mw + 2) ≤ (T.N + G.m + 2) * (Mw + 2) :=
      Nat.mul_le_mul (by omega) le_rfl
    have e : (G.n + 2) * (Mw + 2) = G.n * Mw + 2 * G.n + 2 * Mw + 4 := by ring
    have e2 : 4 * G.n * Mw = 4 * (G.n * Mw) := by ring
    omega
  · have : (T.N + G.m + 2) * 1 ≤ (T.N + G.m + 2) * (Mw + 2) :=
      Nat.mul_le_mul le_rfl (by omega)
    omega
  · have e : 2 ^ (2 * J + 20) * (T.N + G.m + 2) ^ 2 * (Mw + 2) ^ 2 =
        2 ^ 20 * ((2 ^ J * ((T.N + G.m + 2) * (Mw + 2))) *
          (2 ^ J * ((T.N + G.m + 2) * (Mw + 2)))) := by
      rw [show 2 * J + 20 = 20 + (J + J) by omega, pow_add, pow_add]; ring
    rw [e] at hroom
    have h0 := Nat.zero_le ((J + 2) * recCost w A T G P c R)
    omega

/-- **The word bounds of the chain.** -/
theorem ClPre.suWords (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    SuWords w (suVOf GB RB h mem) P.L (c.Δ G) := by
  obtain ⟨Z, hZ1, hθZ, hIZ, hnZ, hroom⟩ := hp.room_core hX
  have hW := hp.words hX
  set J := (GlobL.read mem GB).J
  set INF := (GlobL.read mem GB).INF
  have hb : ∀ r ∈ recRegs GB RB (GlobL.read mem GB) (RecL.read mem RB), r.1 + r.2 ≤ h :=
    hp.below
  have bEX := hb ((GlobL.read mem GB).EXP, (GlobL.read mem GB).m) (by simp [recRegs])
  dsimp only at bEX
  obtain ⟨E', hE', -, -, -, -, hI, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  have hΔI : c.Δ G < INF := hI
  have hJ0 : 128 * P.B * G.n ^ 2 < 2 ^ J := hp.glob.hJ
  have hB1 : 1 ≤ P.B := hp.ok.hB
  set K := 2 ^ J * Z with hK
  have hK1 : 1 ≤ K := Nat.mul_le_mul Nat.one_le_two_pow hZ1
  have hKK : K ≤ K * K := Nat.le_mul_of_pos_left _ (by omega)
  -- `(n + 2)² < 2^J`
  have hn2 : (G.n + 2) ^ 2 ≤ 2 ^ J := by
    have hn1 : 1 ≤ G.n := hp.ok.n_pos hX
    have : (G.n + 2) ^ 2 ≤ 9 * G.n ^ 2 := by nlinarith
    have : 9 * G.n ^ 2 ≤ 128 * P.B * G.n ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  have h4 : 512 * (G.n + 2) ^ 4 ≤ 2 ^ 20 * (K * K) := by
    have e : (G.n + 2) ^ 4 = (G.n + 2) ^ 2 * (G.n + 2) ^ 2 := by ring
    have h5 : (G.n + 2) ^ 2 ≤ Z * Z := by rw [sq]; exact Nat.mul_le_mul hnZ hnZ
    have h6 : (G.n + 2) ^ 2 * (G.n + 2) ^ 2 ≤ 2 ^ J * (Z * Z) := Nat.mul_le_mul hn2 h5
    have h7 : 2 ^ J * (Z * Z) ≤ K * K := by
      rw [hK]
      have : 2 ^ J * (Z * Z) ≤ 2 ^ J * 2 ^ J * (Z * Z) :=
        Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos J))
      calc 2 ^ J * (Z * Z) ≤ 2 ^ J * 2 ^ J * (Z * Z) := this
        _ = 2 ^ J * Z * (2 ^ J * Z) := by ring
    omega
  have hp2 : 2 ^ 2 ^ P.L ≤ 256 * (G.n + 2) ^ 4 := by
    rw [hp.L_eq]; exact two_pow_two_pow_pL_le G.n
  have hLs : P.L < 2 ^ P.L := Nat.lt_two_pow_self
  have hLs2 : 2 ^ P.L < 2 ^ 2 ^ P.L := Nat.pow_lt_pow_right (by norm_num) hLs
  have hJK : J + 5 ≤ 8 * K := by
    have : J < 2 ^ J := Nat.lt_two_pow_self
    have : 2 ^ J ≤ K := Nat.le_mul_of_pos_right _ hZ1
    omega
  have hIK : INF * (J + 5) ≤ 4 * Z * (8 * K) := Nat.mul_le_mul hIZ hJK
  have hZK : Z ≤ K := Nat.le_mul_of_pos_left _ Nat.one_le_two_pow
  have hZK2 : Z * K ≤ K * K := Nat.mul_le_mul_right _ hZK
  have e3 : 4 * Z * (8 * K) = 32 * (Z * K) := by ring
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · show (GlobL.read mem GB).EXP < 2 ^ w
    have := hp.room_h
    omega
  · have : c.Δ G / 8 / P.L ≤ c.Δ G := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
    omega
  · omega
  · omega
  · show INF * (J + 5) + (J + 5) < 2 ^ w
    omega

end MinCostFlow.LowStretch
