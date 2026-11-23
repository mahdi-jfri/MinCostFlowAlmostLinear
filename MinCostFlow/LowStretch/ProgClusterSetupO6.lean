module

public import MinCostFlow.LowStretch.ProgClusterSetupO5

/-!
# The setup of a cluster: the words of the values

The values that the petal searches compute with are words: the products `wU` and `wT2` of
`PW.Ok`, the keys of the arcs (`heads`), and the bounds of `LW` other than `wT1`. Each comes
from the square form `2^(2J+20) (N + m + 2)² (Mw + 2)²` of the room of `ClPre`
(`ClPre.room_sq`), since each is a product of at most
two numbers of size `Mw` (`2^Es`, `INF` and `Δ` are at most about `n Mw`), times numbers of
size `2^J`, `N` and `m`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

/-- The arithmetic of `wU`. -/
theorem wU_arith {b E I Q K Y : ℕ} (hb : b ≤ 3 * K) (hE : E ≤ Y) (hI : I ≤ 4 * (K * Y))
    (hK : 1 ≤ K) (hY : 1 ≤ Y) (hQ : 1 ≤ Q) :
    b * (E * I + E + 1) ≤ 2 ^ 20 * Q ^ 2 * K ^ 2 * Y ^ 2 := by
  have h1 : E * I ≤ 4 * (K * Y * Y) := by
    calc E * I ≤ Y * (4 * (K * Y)) := Nat.mul_le_mul hE hI
      _ = 4 * (K * Y * Y) := by ring
  have h2 : Y ≤ K * Y * Y := by
    calc Y = 1 * 1 * Y := by ring
      _ ≤ K * Y * Y := Nat.mul_le_mul_right _ (Nat.mul_le_mul hK hY)
  have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ
  calc b * (E * I + E + 1) ≤ (3 * K) * (6 * (K * Y * Y)) := Nat.mul_le_mul hb (by omega)
    _ = 18 * 1 * K ^ 2 * Y ^ 2 := by ring
    _ ≤ 2 ^ 20 * Q ^ 2 * K ^ 2 * Y ^ 2 := by gcongr; norm_num

/-- The arithmetic of `wT2`. -/
theorem wT2_arith {M κ nA S Q K Y : ℕ} (hM : M ≤ Y) (hκn : κ + nA ≤ 2 * K) (hκ : κ ≤ K)
    (hS : S ≤ 257 * (Q ^ 2 * K * Y)) (hK : 1 ≤ K) (hY : 1 ≤ Y) (hQ : 1 ≤ Q) :
    8 * M * (4 * (κ + nA) + κ * S) ≤ 2 ^ 20 * Q ^ 2 * K ^ 2 * Y ^ 2 := by
  have h0 : 0 < Q ^ 2 * K * Y :=
    Nat.mul_pos (Nat.mul_pos (pow_pos hQ 2) hK) hY
  have h1 : κ * S ≤ K * (257 * (Q ^ 2 * K * Y)) := Nat.mul_le_mul hκ hS
  have h2 : 4 * (κ + nA) ≤ 8 * (Q ^ 2 * K * Y * K) := by
    have : K ≤ Q ^ 2 * K * Y * K := Nat.le_mul_of_pos_left _ h0
    omega
  have e : K * (257 * (Q ^ 2 * K * Y)) = 257 * (Q ^ 2 * K * Y * K) := by ring
  calc 8 * M * (4 * (κ + nA) + κ * S) ≤ 8 * Y * (265 * (Q ^ 2 * K * Y * K)) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hM) (by omega)
    _ = 2120 * Q ^ 2 * K ^ 2 * Y ^ 2 := by ring
    _ ≤ 2 ^ 20 * Q ^ 2 * K ^ 2 * Y ^ 2 := by gcongr; norm_num

/-- `2^2^L ≤ 256 (2^J)²`, since `2^2^L ≤ 256 (n + 2)⁴` and `(n + 2)² ≤ 2^J`. -/
theorem ClPre.pp_le (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    G.n + 2 ≤ 2 ^ (GlobL.read mem GB).J ∧
      2 ^ 2 ^ P.L ≤ 256 * (2 ^ (GlobL.read mem GB).J) ^ 2 := by
  have hJ0 : 128 * P.B * G.n ^ 2 < 2 ^ (GlobL.read mem GB).J := hp.glob.hJ
  have hB1 : 1 ≤ P.B := hp.ok.hB
  have hn1 : 1 ≤ G.n := hp.ok.n_pos hX
  have hn2 : (G.n + 2) ^ 2 ≤ 2 ^ (GlobL.read mem GB).J := by
    have : (G.n + 2) ^ 2 ≤ 9 * G.n ^ 2 := by nlinarith
    have : 9 * G.n ^ 2 ≤ 128 * P.B * G.n ^ 2 := Nat.mul_le_mul_right _ (by omega)
    omega
  refine ⟨le_trans (by nlinarith) hn2, ?_⟩
  rw [hp.L_eq]
  refine (two_pow_two_pow_pL_le G.n).trans (Nat.mul_le_mul_left _ ?_)
  rw [show (G.n + 2) ^ 4 = ((G.n + 2) ^ 2) ^ 2 by ring]
  exact Nat.pow_le_pow_left hn2 2

/-- `Δ ≤ n Mw` for a bound `Mw` on the weights. -/
theorem ClPre.Δ_le (hp : ClPre w A T G P c R GB RB h mem) {Mw : ℕ}
    (hMw : ∀ p < G.m, G.pω p ≤ Mw) : c.Δ G ≤ G.n * Mw := by
  have hcard : c.X.card ≤ G.n := by
    have := Finset.card_le_card hp.ok.inv.sub
    simpa using this
  exact (Cl.Δ_le_card_mul hp.ok.inv.good.conn hMw).trans (Nat.mul_le_mul_right _ hcard)

/-- **The small values are words**: `INF + 2^(lθ + J + 3) + Δ`, with room to spare. -/
theorem ClPre.small_w (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
   
    16 * ((GlobL.read mem GB).INF + (2 ^ ((RecL.read mem RB).lθ + ((GlobL.read mem GB).J + 3)) +
      c.Δ G)) + G.n < 2 ^ w := by
  obtain ⟨Z, hZ1, hθZ, hIZ, hnZ, hroom⟩ := hp.room_core hX
  obtain ⟨E', hE', -, -, -, -, hI, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  have hΔI : c.Δ G < (GlobL.read mem GB).INF := hI
  have hθ : c.θ = 2 ^ (RecL.read mem RB).lθ := hp.recAt.arcs.th
  set J := (GlobL.read mem GB).J
  set Q := 2 ^ J with hQ
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have e : 2 ^ ((RecL.read mem RB).lθ + (J + 3)) = 8 * (c.θ * Q) := by
    rw [hθ, hQ, pow_add, pow_add]; ring
  have h1 : c.θ * Q ≤ Q * Z := by rw [mul_comm]; exact Nat.mul_le_mul_left _ hθZ
  have h2 : Z ≤ Q * Z := Nat.le_mul_of_pos_left _ hQ1
  have h3 : Q * Z ≤ (Q * Z) * (Q * Z) := Nat.le_mul_of_pos_left _ (by omega)
  rw [e]
  omega

namespace SuAt

variable (a) (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
include hp hX

set_option maxHeartbeats 1000000 in
/-- **The words `wU` and `wT2`.** -/
theorem wU_wT2 :
    (a.W.nA + a.W.L.MM + 1) * (2 ^ a.W.Es * a.W.L.INF + 2 ^ a.W.Es + 1) < 2 ^ w ∧
      8 * a.W.M * (4 * (a.W.κ + a.W.nact) + a.W.κ * a.W.Sm) < 2 ^ w := by
  obtain ⟨Mw, hMw, hINF, hroom⟩ := hp.room_sq
  have hEs := a.pow_Es_le hp hMw
  have hΔ := hp.Δ_le hMw
  obtain ⟨hnQ, hpp⟩ := hp.pp_le hX
  have hN := hp.ok.tree.n_lt
  have hS := hp.ok.S_le
  have hs := hp.ok.s_le
  have hnA := SuAt.nA_le (a := a)
  have hnS : (RecL.read mem RB).nS = R.S.length := hp.recAt.arcs.nS
  have hsl : (RecL.read mem RB).s = R.nodes.length := hp.recAt.arcs.s
  have vnS : SuN.nS 𝔑 = (RecL.read mem RB).nS := rfl
  have vs : SuN.s 𝔑 = (RecL.read mem RB).s := rfl
  have hm : (GlobL.read mem GB).m = G.m := hp.glob.m
  have hn : (GlobL.read mem GB).n = G.n := hp.glob.n
  set J := (GlobL.read mem GB).J
  set K := T.N + G.m + 2 with hK
  set Y := Mw + 2 with hY
  set Q := 2 ^ J with hQ
  have hK1 : 1 ≤ K := by omega
  have hY1 : 1 ≤ Y := by omega
  have hQ1 : 1 ≤ Q := Nat.one_le_two_pow
  have hnK : G.n + 2 ≤ K := by omega
  have hnY : G.n * Mw + 1 ≤ K * Y := by
    have h1 : (G.n + 2) * (Mw + 2) ≤ K * Y := Nat.mul_le_mul hnK le_rfl
    have e : (G.n + 2) * (Mw + 2) = G.n * Mw + 2 * G.n + 2 * Mw + 4 := by ring
    omega
  have e : 2 ^ (2 * J + 20) * K ^ 2 * Y ^ 2 = 2 ^ 20 * Q ^ 2 * K ^ 2 * Y ^ 2 := by
    rw [hQ, ← pow_mul, show 2 * J + 20 = 20 + J * 2 by ring, pow_add]
  rw [e] at hroom
  have e4 : 4 * G.n * Mw = 4 * (G.n * Mw) := by ring
  have h0 := Nat.zero_le ((J + 2) * recCost w A T G P c R)
  have hQ2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ1
  have hQKY : K * Y ≤ Q ^ 2 * K * Y :=
    calc K * Y ≤ Q ^ 2 * (K * Y) := Nat.le_mul_of_pos_left _ hQ2
      _ = Q ^ 2 * K * Y := by ring
  have hQKY' : Q ^ 2 ≤ Q ^ 2 * K * Y := by
    rw [mul_assoc]; exact Nat.le_mul_of_pos_right _ (Nat.mul_le_mul hK1 hY1)
  constructor
  · have k := wU_arith (b := a.hM.nA + (2 * a.hM.nA + SuN.s 𝔑) + 1) (E := 2 ^ a.Es)
      (I := (GlobL.read mem GB).INF) (Q := Q) (K := K) (Y := Y) (by omega) (by omega)
      (by omega) hK1 hY1 hQ1
    show (a.hM.nA + (2 * a.hM.nA + SuN.s 𝔑) + 1) *
      (2 ^ a.Es * (GlobL.read mem GB).INF + 2 ^ a.Es + 1) < 2 ^ w
    omega
  · have hκ : G.m / (G.n * G.n) ≤ G.m := Nat.div_le_self _ _
    have k := wT2_arith (M := 2 ^ a.Es) (κ := G.m / (G.n * G.n) + 1) (nA := a.hM.nA)
      (S := 2 ^ 2 ^ P.L + c.Δ G) (Q := Q) (K := K) (Y := Y) (by omega) (by omega) (by omega)
      (by omega) hK1 hY1 hQ1
    show 8 * 2 ^ a.Es * (4 * ((GlobL.read mem GB).m / ((GlobL.read mem GB).n *
      (GlobL.read mem GB).n) + 1 + a.hM.nA) + ((GlobL.read mem GB).m /
      ((GlobL.read mem GB).n * (GlobL.read mem GB).n) + 1) * (2 ^ 2 ^ P.L + c.Δ G)) < 2 ^ w
    rw [hm, hn]
    omega

theorem wΔ : 3 * a.W.c.Δ a.W.G < 2 ^ w := by
  show 3 * c.Δ G < 2 ^ w
  have := Nat.zero_le (2 ^ ((RecL.read mem RB).lθ + ((GlobL.read mem GB).J + 3)))
  exact lt_of_le_of_lt (by omega) (hp.small_w hX)

theorem wd : ∀ x ∈ a.W.c.X, 4 * a.W.c.d a.W.G a.W.c.x0 x < 2 ^ w := by
  intro x hx
  have : c.d G c.x0 x ≤ c.Δ G := Cl.d_le_Δ (G := G) (c := c) hx
  show 4 * c.d G c.x0 x < 2 ^ w
  have := Nat.zero_le (2 ^ ((RecL.read mem RB).lθ + ((GlobL.read mem GB).J + 3)))
  exact lt_of_le_of_lt (by omega) (hp.small_w hX)

theorem heads_w :
    (GlobL.read mem GB).INF + (2 ^ ((RecL.read mem RB).lθ + ((GlobL.read mem GB).J + 3)) +
      c.Δ G) < 2 ^ w := by
  have := hp.small_w hX; omega

/-- The bounds of `LW` and `SetupOut` on the ranges of the special petal. -/
theorem loS_w (hP : P = par G.n G.m) :
    c.loS G + (P.L + 1) * a.W.bw + 2 < 2 ^ w ∧ c.loS G + (P.L + 1) * a.W.bw ≤ a.W.Rm ∧
      c.loS G + (P.L + 1) * a.W.bw < a.W.L.INF ∧
      (5 * c.Δ G < 8 * c.d G c.x0 c.t → c.loS G + P.L * a.W.bw < c.d G c.x0 c.t) ∧
      c.t < 2 ^ w := by
  have := hp.small_w hX
  obtain ⟨E', hE', -, -, -, -, hI, -⟩ := hp.drawPre hX
  obtain rfl := DWE.eq_of_args hE'
  have hΔI : c.Δ G < (GlobL.read mem GB).INF := hI
  have hdt : c.d G c.x0 c.t ≤ c.Δ G := Cl.d_le_Δ hp.ok.inv.t_mem
  have hlo : c.loS G + (P.L + 1) * (c.Δ G / 8 / P.L) ≤ c.Δ G :=
    loS_bw_le (Δ := c.Δ G) (d := c.d G c.x0 c.t) (L := P.L) hdt
  have := Nat.zero_le (2 ^ ((RecL.read mem RB).lθ + ((GlobL.read mem GB).J + 3)))
  have hΔ := setup_hΔ hp.ok hP hX
  have hL : 1 ≤ 8 * P.L * (Cl.lam P 0 + 3) := by
    have : 1 ≤ P.L := by rw [hp.L_eq]; have := log_pa_le G.n; omega
    have : 1 ≤ 8 * P.L := by omega
    exact this.trans (Nat.le_mul_of_pos_right _ (by omega))
  have ht : c.t < G.n := Finset.mem_range.mp (hp.ok.inv.sub hp.ok.inv.t_mem)
  have hbw : a.W.bw = c.Δ G / 8 / P.L := rfl
  rw [hbw]
  show _ ∧ _ ≤ 2 * c.Δ G - 1 ∧ _ < (GlobL.read mem GB).INF ∧ _ ∧ _
  have hsw := hp.small_w hX
  refine ⟨?_, by omega, by omega, fun h5 => loS_far (by omega) h5, ?_⟩
  · have h1 : c.loS G + (P.L + 1) * (c.Δ G / 8 / P.L) + 2 ≤
        16 * ((GlobL.read mem GB).INF + (2 ^ ((RecL.read mem RB).lθ +
          ((GlobL.read mem GB).J + 3)) + c.Δ G)) + G.n := by omega
    exact lt_of_le_of_lt h1 hsw
  · have h1 : c.t ≤ 16 * ((GlobL.read mem GB).INF + (2 ^ ((RecL.read mem RB).lθ +
          ((GlobL.read mem GB).J + 3)) + c.Δ G)) + G.n := by omega
    exact lt_of_le_of_lt h1 hsw

end SuAt

end MinCostFlow.LowStretch
