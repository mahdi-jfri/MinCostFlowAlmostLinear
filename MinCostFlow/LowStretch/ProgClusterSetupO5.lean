module

public import MinCostFlow.LowStretch.ProgClusterSetupR1

/-!
# The setup of a cluster: the layout that the setup leaves

The arrays of the setting `a.W` follow each other in the order of `SuN`, and all end by the
end `hS` of the heap, which is a word (`ClPre.hS_lt`). This file gives the facts of the layout
in `PW.Ok` (`lay`, `lES`, `hR`, `hCTL`, `hSUM`, `hSL`) and the word bounds on addresses
(`wSL`, `fits`, `wR2`, `wL`, `wSQ`, `wP2`, `wNXT`), and those of `LLay`.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

/-- The addresses up to the queues are below the queues. -/
theorem suN_z_le_D {x y u v : ℕ} (hx : x ≤ 23) (hy : y ≤ 26) (hu : u ≤ 2) (hv : v ≤ 16) :
    SuN.z 𝔑 x y u v ≤ SuN.D 𝔑 := by
  unfold SuN.D SuN.z
  have := Nat.mul_le_mul_right (SuN.nS 𝔑) hx
  have := Nat.mul_le_mul_right (SuN.s 𝔑) hy
  have := Nat.mul_le_mul_right (SuN.L 𝔑) hu
  omega

theorem ClPre.D_w (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    SuN.D 𝔑 + SuN.s 𝔑 + 16 < 2 ^ w ∧ SuN.L 𝔑 + 16 ≤ SuN.D 𝔑 := by
  have := hp.hS_lt hX
  have := (SuN.RR_eq 𝔑)
  simp only [SuN.hS, SuN.r] at *
  have e : SuN.D 𝔑 = SuN.z 𝔑 23 26 2 16 := rfl
  simp only [SuN.z] at e
  omega

namespace SuAt

variable (a)

/-- **The order of the arrays.** -/
theorem lay :
    a.W.L.LO + a.W.L.NN ≤ a.W.L.HD ∧ a.W.L.HI + a.W.L.NN ≤ a.W.L.HD ∧
      a.W.L.HD + a.W.L.MM ≤ a.W.L.CS ∧ a.W.L.CS + a.W.L.MM ≤ a.W.L.CL ∧
      a.W.L.CL + a.W.L.MM ≤ a.W.L.OK ∧ a.W.L.OK + a.W.L.NN ≤ a.W.NXT ∧
      a.W.NXT + a.W.L.NN ≤ a.W.ORD ∧ a.W.ORD + a.W.L.MM ≤ a.W.AS ∧
      a.W.AS + 2 * a.W.nA ≤ a.W.EXP ∧ a.W.SQ + a.W.Lb + 2 ≤ a.W.P2 ∧
      a.W.P2 + a.W.Lb + 2 ≤ a.W.L.TS ∧ a.W.L.TS + 5 * a.W.L.NN ≤ a.W.L.D := by
  have := SuAt.nA_le (a := a)
  have hL : SuN.L 𝔑 = P.L := rfl
  show SuN.z 𝔑 10 12 0 2 + (SuN.s 𝔑 + 1) ≤ SuN.z 𝔑 12 15 0 5 ∧
    SuN.z 𝔑 10 12 0 3 + (SuN.s 𝔑 + 1) ≤ SuN.z 𝔑 12 15 0 5 ∧
    SuN.z 𝔑 12 15 0 5 + (2 * a.hM.nA + SuN.s 𝔑) ≤ SuN.z 𝔑 14 16 0 5 ∧
    SuN.z 𝔑 14 16 0 5 + (2 * a.hM.nA + SuN.s 𝔑) ≤ SuN.z 𝔑 16 17 0 5 ∧
    SuN.z 𝔑 16 17 0 5 + (2 * a.hM.nA + SuN.s 𝔑) ≤ SuN.z 𝔑 18 18 0 5 ∧
    SuN.z 𝔑 18 18 0 5 + (SuN.s 𝔑 + 1) ≤ SuN.z 𝔑 18 19 0 6 ∧
    SuN.z 𝔑 18 19 0 6 + (SuN.s 𝔑 + 1) ≤ SuN.z 𝔑 18 20 0 7 ∧
    SuN.z 𝔑 18 20 0 7 + (2 * a.hM.nA + SuN.s 𝔑) ≤ SuN.z 𝔑 20 21 0 7 ∧
    SuN.z 𝔑 20 21 0 7 + 2 * a.hM.nA ≤ SuN.z 𝔑 22 21 0 7 ∧
    SuN.z 𝔑 23 21 0 7 + P.L + 2 ≤ SuN.z 𝔑 23 21 1 9 ∧
    SuN.z 𝔑 23 21 1 9 + P.L + 2 ≤ SuN.z 𝔑 23 21 2 11 ∧
    SuN.z 𝔑 23 21 2 11 + 5 * (SuN.s 𝔑 + 1) ≤ SuN.D 𝔑
  simp only [SuN.D, SuN.z, hL]
  omega

theorem lES : a.W.EXP ≤ a.W.SQ := by
  show SuN.z 𝔑 22 21 0 7 ≤ SuN.z 𝔑 23 21 0 7
  simp only [SuN.z]; omega

theorem hRR : a.W.L.D + pqSize a.W.L.J a.W.L.A ≤ a.W.RR :=
  (SuN.RR_eq 𝔑).ge

theorem hCTL : a.W.RR + 2 ≤ a.W.CTL := by
  show SuN.RR 𝔑 + 2 ≤ SuN.r 𝔑 0 2
  simp only [SuN.r]; omega

theorem hSUM : a.W.CTL + 4 ≤ a.W.SUM := by
  show SuN.r 𝔑 0 2 + 4 ≤ SuN.r 𝔑 0 6
  simp only [SuN.r]; omega

theorem hSL : a.W.SUM + 5 ≤ a.W.SL := by
  show SuN.r 𝔑 0 6 + 5 ≤ SuN.r 𝔑 0 11
  simp only [SuN.r]; omega

variable (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
include hp hX

theorem wSL : a.W.SL + a.W.L.NN + 1 < 2 ^ w := by
  have := hp.hS_lt hX
  show SuN.r 𝔑 0 11 + (SuN.s 𝔑 + 1) + 1 < 2 ^ w
  simp only [SuN.hS, SuN.r] at *; omega

theorem wR2 : a.W.RR + 2 < 2 ^ w := by
  have := hp.hS_lt hX
  show SuN.RR 𝔑 + 2 < 2 ^ w
  simp only [SuN.hS, SuN.r] at *; omega

theorem fits : PQFits w a.W.L.D a.W.L.J a.W.L.A a.W.L.INF := by
  have h1 := a.wR2 hp hX
  have h2 := (hp.suWords hX).hINF
  have h3 := a.hRR
  refine ⟨by omega, h2, ?_⟩
  have := hp.room_h; have : 2 ^ 2 < 2 ^ 24 := by norm_num
  omega

theorem wL : a.W.Lb + 2 < 2 ^ w := by
  have := hp.D_w hX
  show SuN.L 𝔑 + 2 < 2 ^ w
  omega

theorem wSQ : a.W.SQ + a.W.Lb + 1 < 2 ^ w := by
  have := hp.D_w hX
  have := suN_z_le_D (GB := GB) (RB := RB) (h := h) (mem := mem) (P := P) (x := 23) (y := 21)
    (u := 1) (v := 9) (by omega) (by omega) (by omega) (by omega)
  show SuN.z 𝔑 23 21 0 7 + SuN.L 𝔑 + 1 < 2 ^ w
  simp only [SuN.z] at *; omega

theorem wP2 : a.W.P2 + a.W.Lb + 1 < 2 ^ w := by
  have := hp.D_w hX
  have := suN_z_le_D (GB := GB) (RB := RB) (h := h) (mem := mem) (P := P) (x := 23) (y := 21)
    (u := 2) (v := 11) (by omega) (by omega) (by omega) (by omega)
  show SuN.z 𝔑 23 21 1 9 + SuN.L 𝔑 + 1 < 2 ^ w
  simp only [SuN.z] at *; omega

theorem wNXT : a.W.NXT + a.W.L.NN < 2 ^ w := by
  have := hp.D_w hX
  have := suN_z_le_D (GB := GB) (RB := RB) (h := h) (mem := mem) (P := P) (x := 18) (y := 20)
    (u := 0) (v := 7) (by omega) (by omega) (by omega) (by omega)
  show SuN.z 𝔑 18 19 0 6 + (SuN.s 𝔑 + 1) < 2 ^ w
  simp only [SuN.z] at *; omega

/-- **The layout of the outputs.** -/
theorem lLay : a.W.LLay (suTA 𝔑) (suLA 𝔑) w := by
  have := hp.hS_lt hX
  have := SuAt.nA_le (a := a)
  have hs := SuAt.W_s (a := a) hp
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show SuN.r 𝔑 0 11 + (SuN.s 𝔑 + 1) + 1 ≤ SuN.r 𝔑 1 13
    simp only [SuN.r]; omega
  · rw [hs]; show SuN.r 𝔑 1 13 + SuN.s 𝔑 ≤ SuN.r 𝔑 2 13
    simp only [SuN.r]; omega
  · rw [hs]; show SuN.r 𝔑 2 13 + SuN.s 𝔑 + 1 ≤ SuN.r 𝔑 3 14
    simp only [SuN.r]; omega
  · rw [hs]; show SuN.r 𝔑 3 14 + SuN.s 𝔑 + 1 ≤ SuN.r 𝔑 4 15
    simp only [SuN.r]; omega
  · rw [hs]; show SuN.r 𝔑 4 15 + SuN.s 𝔑 + 1 ≤ SuN.r 𝔑 5 16
    simp only [SuN.r]; omega
  · rw [hs]; show SuN.r 𝔑 5 16 + SuN.s 𝔑 < 2 ^ w
    simp only [SuN.hS, SuN.r] at *; omega
  · rw [hs]
    show SuN.z 𝔑 0 1 0 1 + SuN.s 𝔑 ≤ SuN.z 𝔑 12 15 0 5 ∧
      SuN.z 𝔑 0 2 0 1 + SuN.s 𝔑 ≤ SuN.z 𝔑 12 15 0 5 ∧
      SuN.z 𝔑 0 3 0 1 + SuN.s 𝔑 ≤ SuN.z 𝔑 12 15 0 5 ∧
      SuN.z 𝔑 0 4 0 1 + SuN.s 𝔑 ≤ SuN.z 𝔑 12 15 0 5 ∧
      SuN.H 𝔑 + 16 * SuN.nS 𝔑 + 4 * SuN.s 𝔑 + 5 + SuN.s 𝔑 ≤ SuN.z 𝔑 12 15 0 5
    simp only [SuN.z, SuN.Z]; omega

end SuAt

end MinCostFlow.LowStretch
