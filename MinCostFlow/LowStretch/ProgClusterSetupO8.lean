module

public import MinCostFlow.LowStretch.ProgClusterSetupO7

/-!
# The setup of a cluster: the word facts of the loop

The word facts `LW` of the petal loop hold for the setting `a.W` (`SuAt.lw`). Every register
of the loop is a word (`wR`): the addresses end by the end of the heap, and the values (`Es`,
`M`, `κ`, the number of active pairs, `bw` and `Δ`) are factors of the words `wT2` and `wΔ`.
The product `wT1` needs the room `SuRoom3` (`SuAt.wT1`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st} {F : ℕ → ℕ}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

namespace SuAt

variable (a) (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
  (hP : P = par G.n G.m)
include hp hX hP

set_option maxHeartbeats 4000000 in
/-- **The registers of the loop are words.** -/
theorem wR : ∀ x ∈ a.W.LReg (suTA 𝔑) (suLA 𝔑) (a.W.c.Δ a.W.G), x < 2 ^ w := by
  obtain ⟨l1, l2, l3, l4, l5, l6, l7, l8, l9, l10, l11, l12⟩ := a.lay
  have hR := a.hRR; have hCTL := a.hCTL; have hSUM := a.hSUM; have hSL := a.hSL
  have wSL := a.wSL hp hX; have hES := a.lES
  have wSQ := a.wSQ hp hX; have wP2 := a.wP2 hp hX; have wNXT := a.wNXT hp hX
  have wL := a.wL hp hX; have wR2 := a.wR2 hp hX
  obtain ⟨f1, f2, f3⟩ := a.fits hp hX
  have hL := a.lLay hp hX
  have hpl := hL.pl; have hpo := hL.po; have hct := hL.ct; have hcc := hL.cc
  have hpt := hL.pt; have wpt := hL.wpt
  obtain ⟨t1, t2, t3, t4, t5⟩ := hL.ta
  have wΔ := a.wΔ hp hX
  have wT2 := (a.wU_wT2 hp hX).2
  have hs := SuAt.W_s (a := a) hp
  have hNN : a.W.L.NN = a.W.s + 1 := by rw [hs]; rfl
  have hJ : 0 < a.W.L.J := by show 0 < _ + 5; omega
  have hIJ : a.W.L.INF ≤ a.W.L.INF * a.W.L.J := Nat.le_mul_of_pos_right _ hJ
  have hAD : a.W.L.A ≤ a.W.L.D := by
    show SuN.A2 𝔑 ≤ SuN.D 𝔑
    unfold SuN.A2 SuN.D SuN.z; omega
  have hEs : a.W.Es < a.W.M := Nat.lt_two_pow_self
  have hκ : 1 ≤ a.W.κ := by rw [a.κ_eq hp hP, hP]; simp [par, pκ]
  have hM : 1 ≤ a.W.M := Nat.one_le_two_pow
  have hXX : 4 * (a.W.κ + a.W.nact) + a.W.κ * a.W.Sm ≤
      8 * a.W.M * (4 * (a.W.κ + a.W.nact) + a.W.κ * a.W.Sm) :=
    Nat.le_mul_of_pos_left _ (by omega)
  have hMM : a.W.M ≤ 8 * a.W.M * (4 * (a.W.κ + a.W.nact) + a.W.κ * a.W.Sm) :=
    calc a.W.M = a.W.M * 1 := by ring
      _ ≤ 8 * a.W.M * (4 * (a.W.κ + a.W.nact) + a.W.κ * a.W.Sm) := by
        rw [show 8 * a.W.M * (4 * (a.W.κ + a.W.nact) + a.W.κ * a.W.Sm) =
          a.W.M * (8 * (4 * (a.W.κ + a.W.nact) + a.W.κ * a.W.Sm)) by ring]
        exact Nat.mul_le_mul_left _ (by omega)
  have hbw : a.W.bw ≤ a.W.c.Δ a.W.G := (Nat.div_le_self _ _).trans (Nat.div_le_self _ _)
  intro x hx
  simp only [PW.LReg, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | omega
    | (show 0 < 2 ^ w; exact Nat.two_pow_pos w)

theorem lw (h3 : SuRoom3 w T G h) : a.W.LW (suTA 𝔑) (suLA 𝔑) w := by
  obtain ⟨b1, b2, b3, -, -⟩ := a.loS_w hp hX hP
  have k := a.wT1 hp hX h3
  have hLb : a.W.Lb = P.L := rfl
  rw [hLb] at k
  have m1 : (a.W.Lb + 1) * a.W.bw = (P.L + 1) * a.W.bw := by rw [hLb]
  refine ⟨a.wR hp hX hP, by omega, lt_of_le_of_lt ?_ k, by omega, by omega, a.wΔ hp hX,
    a.wd hp hX⟩
  refine Nat.mul_le_mul_right _ (Nat.add_le_add_left (Nat.mul_le_mul_right _ ?_) _)
  omega

end SuAt

end MinCostFlow.LowStretch
