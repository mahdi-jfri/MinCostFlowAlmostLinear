module

public import MinCostFlow.LowStretch.ProgClusterSetupDf

/-!
# The setup of a cluster: the memory after the setup

The memory `F` after the stores of the block (`SuFin`) agrees with the memory `P3` before them
outside the block. So every fact of `SuAt.low`, `SuAt.pgc`, … holds for `F` at the cells from
`h + 51` on. This file restates them for `F` (`SuFin.low`, `SuFin.pgc`, …), and gives the
facts of the graph of `pgP` in `F` (`SuFin.pgPost`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st} {F : ℕ → ℕ}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

theorem suN_hZ (GB RB h : ℕ) (mem : ℕ → ℕ) (L : ℕ) : h + 51 ≤ ((suVOf GB RB h mem).N L).Z := by
  simp only [SuN.Z, SuN.H, SuV.N, suVOf]; omega

namespace SuFin

variable (hf : SuFin a F)
include hf

/-- Below `h`, the memory after the setup is the memory at the start. -/
theorem lowh {x : ℕ} (hx : x < h) : F x = mem x := by
  rw [hf.fr x (Or.inl hx), a.low (x := x) (by have := suN_hZ GB RB h mem P.L; simp only [SuN.z]; omega)]
  exact a.hM.low_h (by omega)

/-- Between the block and the graph of `pgP`: the memory after `actP`. -/
theorem low {x : ℕ} (h1 : h + 51 ≤ x) (h2 : x < SuN.z 𝔑 2 8 0 2) : F x = a.M4 x := by
  rw [hf.fr x (Or.inr h1), a.low h2]

/-- The graph of `pgP`. -/
theorem pgc {x : ℕ} (h1 : SuN.z 𝔑 2 8 0 2 ≤ x) (h2 : x ≤ SuN.z 𝔑 18 18 0 5 + SuN.s 𝔑) :
    F x = a.M5 x := by
  rw [hf.fr x (Or.inr (by have := suN_hZ GB RB h mem P.L; simp only [SuN.z] at *; omega)), a.pgc h1 h2]

theorem nxt {i : ℕ} (hi : i < SuN.s 𝔑) :
    F (SuN.z 𝔑 18 19 0 6 + i) = a.M4 (SuN.Z 𝔑 + i) := by
  rw [hf.fr _ (Or.inr (by have := suN_hZ GB RB h mem P.L; simp only [SuN.z] at *; omega)), a.nxt hi]

theorem ordc {i : ℕ} (hi : i < 2 * a.hM.nA + SuN.s 𝔑) :
    F (SuN.z 𝔑 18 20 0 7 + i) = a.M5 (SuN.z 𝔑 10 14 0 5 + i) := by
  rw [hf.fr _ (Or.inr (by have := suN_hZ GB RB h mem P.L; simp only [SuN.z] at *; omega)), a.ordc hi]

theorem as {i : ℕ} (hi : i < 2 * a.hM.nA) : F (SuN.z 𝔑 20 21 0 7 + i) = i / 2 := by
  rw [hf.fr _ (Or.inr (by have := suN_hZ GB RB h mem P.L; simp only [SuN.z] at *; omega)), a.as hi]

theorem exp {i : ℕ} (hi : i < a.hM.nA)
    (hy : (suVOf GB RB h mem).EXP + a.M4 (SuN.z 𝔑 0 8 0 2 + 2 * i) < SuN.z 𝔑 2 8 0 2) :
    F (SuN.z 𝔑 22 21 0 7 + i) =
      a.M4 ((suVOf GB RB h mem).EXP + a.M4 (SuN.z 𝔑 0 8 0 2 + 2 * i)) := by
  rw [hf.fr _ (Or.inr (by have := suN_hZ GB RB h mem P.L; simp only [SuN.z] at *; omega)), a.exp hi hy]

theorem sq {i : ℕ} (hi : i < P.L + 2) :
    F (SuN.z 𝔑 23 21 0 7 + i) = c.Δ G / 8 / P.L / (2 ^ (P.L - (i - 1)) + 3) := by
  rw [hf.fr _ (Or.inr (by have := suN_hZ GB RB h mem P.L; simp only [SuN.z] at *; omega)), a.sq hi]

theorem p2 {i : ℕ} (hi : i < P.L + 2) : F (SuN.z 𝔑 23 21 1 9 + i) = 2 ^ 2 ^ (P.L - i) := by
  rw [hf.fr _ (Or.inr (by have := suN_hZ GB RB h mem P.L; simp only [SuN.z] at *; omega)), a.p2 hi]

theorem zero (hp : ClPre w A T G P c R GB RB h mem) {x : ℕ}
    (hx : (SuN.z 𝔑 23 21 2 11 ≤ x ∧ x < SuN.D 𝔑) ∨ SuN.RR 𝔑 ≤ x) : F x = 0 := by
  have : SuN.z 𝔑 23 21 2 11 ≤ x := by
    rcases hx with hx | hx
    · exact hx.1
    · have := (SuN.RR_eq' 𝔑); simp only [SuN.D, SuN.z] at *; omega
  rw [hf.fr _ (Or.inr (by have := suN_hZ GB RB h mem P.L; simp only [SuN.z] at *; omega)), a.zero hp hx]

theorem nxt_s (hp : ClPre w A T G P c R GB RB h mem) :
    F (SuN.z 𝔑 18 19 0 6 + SuN.s 𝔑) = 0 := by
  rw [hf.fr _ (Or.inr (by have := suN_hZ GB RB h mem P.L; simp only [SuN.z] at *; omega)), a.nxt_s hp]

/-- The queues of the petal searches. -/
theorem queue {x : ℕ} (h1 : SuN.D 𝔑 ≤ x) : F x = a.P3 x :=
  hf.fr x (Or.inr (by have := suN_hZ GB RB h mem P.L; simp only [SuN.D, SuN.z] at *; omega))

end SuFin

end MinCostFlow.LowStretch
