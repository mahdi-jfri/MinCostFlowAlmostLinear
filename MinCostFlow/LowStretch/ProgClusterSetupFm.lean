module

public import MinCostFlow.LowStretch.ProgClusterSetupWd

/-!
# The setup of a cluster: the memory before the stores of the block

Before the stores of the block, the memory `P3` of `SuAt` holds what each call left in its own
cells: below the graph of `pgP` the memory after `actP`, then the graph of `pgP`, the copy `NXT`
of the parents, the copy of `ORD`, the halves `AS`, the exponents `EXP` and the tables `SQ`
and `P2`. Every cell from `Z` on that no call writes is still `0`, since the memory is zero from
`h` on (`ClPre.zero`) and each call writes only its own cells. This file proves these facts from
the frames of the calls (`SuAt.low`, `SuAt.pgc`, `SuAt.nxt`, …, `SuAt.zero`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State}

namespace SuAt

variable (a : SuAt w T G P c R GB RB h mem st)

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

/-- The frame of `pgP`. -/
theorem pg_fr (x : ℕ) (hx : x < (SuN.z 𝔑) 2 8 0 2 ∨ (SuN.z 𝔑) 18 18 0 5 + (SuN.s 𝔑) < x) :
    a.M5 x = a.M4 x :=
  (a.pg _ rfl).2.2.2.2.2.2.2.2.2.1 x (fun h' => by
    have e1 : (suPGA (suVOf GB RB h mem) P.L a.hM.nA).TL = (SuN.z 𝔑) 2 8 0 2 := rfl
    have e2 : (suPGA (suVOf GB RB h mem) P.L a.hM.nA).OK = (SuN.z 𝔑) 18 18 0 5 := rfl
    have e3 : (suPGA (suVOf GB RB h mem) P.L a.hM.nA).s = (SuN.s 𝔑) := rfl
    rw [e1, e2, e3] at h'; omega)

/-- From the copy `NXT` on, the memory before the stores is the memory after `pgP`, apart from
the tables. -/
theorem fr_hi (x : ℕ) (h1 : x < (SuN.z 𝔑) 18 19 0 6 ∨ (SuN.z 𝔑) 18 19 0 6 + (SuN.s 𝔑) ≤ x)
    (h2 : x < (SuN.z 𝔑) 18 20 0 7 ∨ (SuN.z 𝔑) 18 20 0 7 + (2 * a.hM.nA + (SuN.s 𝔑)) ≤ x)
    (h3 : x < (SuN.z 𝔑) 20 21 0 7 ∨ (SuN.z 𝔑) 20 21 0 7 + 2 * a.hM.nA ≤ x)
    (h4 : x < (SuN.z 𝔑) 22 21 0 7 ∨ (SuN.z 𝔑) 22 21 0 7 + a.hM.nA ≤ x)
    (h5 : x < (SuN.z 𝔑) 23 21 1 9 ∨ (SuN.z 𝔑) 23 21 1 9 + (P.L + 2) ≤ x)
    (h6 : x < (SuN.z 𝔑) 23 21 0 7 ∨ (SuN.z 𝔑) 23 21 0 7 + (P.L + 2) ≤ x)
    (h7 : x < (SuN.D 𝔑)) : a.P3 x = a.M5 x := by
  have eD : (SuN.D 𝔑) = (SuN.z 𝔑) 23 26 2 16 := rfl
  rw [a.u3f x (fun h' => by unfold pqOut at h'; omega) (by omega) (by omega) (by omega),
    a.u2f x h6, a.u1f x h5, a.t4f x h4, a.t3f x h3, a.t2f x h2, a.t1f x h1]

/-- **Below the graph of `pgP`** the memory before the stores is the memory after `actP`. -/
theorem low {x : ℕ} (hx : x < (SuN.z 𝔑 2 8 0 2)) : a.P3 x = a.M4 x := by
  rw [a.fr_hi x (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z, SuN.D] at *; omega)]
  exact a.pg_fr x (Or.inl hx)

/-- The graph of `pgP` is kept. -/
theorem pgc {x : ℕ} (h1 : SuN.z 𝔑 2 8 0 2 ≤ x) (h2 : x ≤ SuN.z 𝔑 18 18 0 5 + SuN.s 𝔑) :
    a.P3 x = a.M5 x :=
  a.fr_hi x (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z, SuN.D] at *; omega)

/-- The copy `NXT` of the parents `PAR`. -/
theorem nxt {i : ℕ} (hi : i < SuN.s 𝔑) :
    a.P3 (SuN.z 𝔑 18 19 0 6 + i) = a.M4 (SuN.Z 𝔑 + i) := by
  have e : a.P3 (SuN.z 𝔑 18 19 0 6 + i) = a.N1 (SuN.z 𝔑 18 19 0 6 + i) := by
    have eD : SuN.D 𝔑 = SuN.z 𝔑 23 26 2 16 := rfl
    rw [a.u3f _ (fun h' => by unfold pqOut at h'; simp only [SuN.z] at *; omega)
      (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
      (by simp only [SuN.z] at *; omega), a.u2f _ (by simp only [SuN.z] at *; omega),
      a.u1f _ (by simp only [SuN.z] at *; omega), a.t4f _ (by simp only [SuN.z] at *; omega),
      a.t3f _ (by simp only [SuN.z] at *; omega), a.t2f _ (by simp only [SuN.z] at *; omega)]
  rw [e, a.t1 i hi, a.pg_fr _ (Or.inl (by simp only [SuN.z] at *; omega))]

/-- The copy of `ORD`. -/
theorem ordc {i : ℕ} (hi : i < 2 * a.hM.nA + SuN.s 𝔑) :
    a.P3 (SuN.z 𝔑 18 20 0 7 + i) = a.M5 (SuN.z 𝔑 10 14 0 5 + i) := by
  have hnA : a.hM.nA ≤ SuN.nS 𝔑 := selL_length_le _ _ _ _ _
  have eD : SuN.D 𝔑 = SuN.z 𝔑 23 26 2 16 := rfl
  rw [a.u3f _ (fun h' => by unfold pqOut at h'; simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega), a.u2f _ (by simp only [SuN.z] at *; omega),
    a.u1f _ (by simp only [SuN.z] at *; omega), a.t4f _ (by simp only [SuN.z] at *; omega),
    a.t3f _ (by simp only [SuN.z] at *; omega), a.t2 i hi,
    a.t1f _ (by simp only [SuN.z] at *; omega)]

/-- The halves `AS`. -/
theorem as {i : ℕ} (hi : i < 2 * a.hM.nA) : a.P3 (SuN.z 𝔑 20 21 0 7 + i) = i / 2 := by
  have hnA : a.hM.nA ≤ SuN.nS 𝔑 := selL_length_le _ _ _ _ _
  have eD : SuN.D 𝔑 = SuN.z 𝔑 23 26 2 16 := rfl
  rw [a.u3f _ (fun h' => by unfold pqOut at h'; simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega), a.u2f _ (by simp only [SuN.z] at *; omega),
    a.u1f _ (by simp only [SuN.z] at *; omega), a.t4f _ (by simp only [SuN.z] at *; omega),
    a.t3 i hi]

/-- Below the halves, the memory after the copies is the memory after `actP`. -/
theorem n3_low {x : ℕ} (hx : x < SuN.z 𝔑 2 8 0 2) : a.N3 x = a.M4 x := by
  rw [a.t3f x (Or.inl (by simp only [SuN.z] at *; omega)),
    a.t2f x (Or.inl (by simp only [SuN.z] at *; omega)),
    a.t1f x (Or.inl (by simp only [SuN.z] at *; omega)), a.pg_fr x (Or.inl hx)]

/-- The exponents `EXP`. -/
theorem exp {i : ℕ} (hi : i < a.hM.nA)
    (hy : (suVOf GB RB h mem).EXP + a.M4 (SuN.z 𝔑 0 8 0 2 + 2 * i) < SuN.z 𝔑 2 8 0 2) :
    a.P3 (SuN.z 𝔑 22 21 0 7 + i) =
      a.M4 ((suVOf GB RB h mem).EXP + a.M4 (SuN.z 𝔑 0 8 0 2 + 2 * i)) := by
  have hnA : a.hM.nA ≤ SuN.nS 𝔑 := selL_length_le _ _ _ _ _
  have eD : SuN.D 𝔑 = SuN.z 𝔑 23 26 2 16 := rfl
  rw [a.u3f _ (fun h' => by unfold pqOut at h'; simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega), a.u2f _ (by simp only [SuN.z] at *; omega),
    a.u1f _ (by simp only [SuN.z] at *; omega), a.t4 i hi,
    a.n3_low (x := SuN.z 𝔑 0 8 0 2 + 2 * i) (by simp only [SuN.z] at *; omega), a.n3_low hy]

/-- The table `SQ`. -/
theorem sq {i : ℕ} (hi : i < P.L + 2) :
    a.P3 (SuN.z 𝔑 23 21 0 7 + i) = c.Δ G / 8 / P.L / (2 ^ (P.L - (i - 1)) + 3) := by
  have eD : SuN.D 𝔑 = SuN.z 𝔑 23 26 2 16 := rfl
  have eL : SuN.L 𝔑 = P.L := rfl
  rw [a.u3f _ (fun h' => by unfold pqOut at h'; simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega), a.u2 i hi]

/-- The table `P2`. -/
theorem p2 {i : ℕ} (hi : i < P.L + 2) :
    a.P3 (SuN.z 𝔑 23 21 1 9 + i) = 2 ^ 2 ^ (P.L - i) := by
  have eD : SuN.D 𝔑 = SuN.z 𝔑 23 26 2 16 := rfl
  have eL : SuN.L 𝔑 = P.L := rfl
  rw [a.u3f _ (fun h' => by unfold pqOut at h'; simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega), a.u2f _ (by simp only [SuN.z] at *; omega), a.u1 i hi]

/-- **From the graph of `pgP` on, the memory after `actP` is zero.** -/
theorem m4_zero (hp : ClPre w A T G P c R GB RB h mem) {x : ℕ} (hx : SuN.z 𝔑 2 8 0 2 ≤ x) :
    a.M4 x = 0 := by
  have hZ : h + 51 ≤ SuN.Z 𝔑 := by simp only [SuN.Z, SuN.H, SuV.N, suVOf]; omega
  have hVf := hp.hfV a.hM.first hZ a.hM.tr_fr
  have hs : (RecL.read mem RB).s = R.nodes.length := hp.recAt.arcs.s
  have es : SuN.s 𝔑 = (RecL.read mem RB).s := rfl
  have en : SuN.nS 𝔑 = (RecL.read mem RB).nS := rfl
  have ds : (suVOf GB RB h mem).dwE.s = (RecL.read mem RB).s := rfl
  have hnu : ∀ j < (RecL.read mem RB).nH, ((suVOf GB RB h mem).dwE.hfx (SuN.Z 𝔑)
      (RecL.read mem RB).nH (RecL.read mem RB).HW).nu a.M2 j < (RecL.read mem RB).s :=
    fun j hj => by rw [hVf.nu_eq hj, hs]; exact hVf.ok.sv_lt (hVf.step hj).2.1
  simp only [SuN.z] at hx
  rw [a.hM.ac_fr x (fun h' => by omega), a.hM.hf_fr x (fun j hj => by
    have := hnu j hj
    generalize ((suVOf GB RB h mem).dwE.hfx (SuN.Z 𝔑) (RecL.read mem RB).nH
      (RecL.read mem RB).HW).nu a.M2 j = y at *
    simp only [DWE.hfx]; refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega),
    a.hM.tr_fr x (fun ho => by
      have h1 := ho.2; simp only [DWE.tf] at h1; omega)]
  obtain ⟨-, -, -, -, -, -, -, -, -, hfar⟩ := a.hM.first.run
  rw [hfar x (Or.inr (by rw [SuV.drawEnd_eq (L := P.L)]; omega))]
  exact hp.zero x (by omega)

/-- **The cells that no call writes are zero**: the stamps `TS` and everything from `RR` on. -/
theorem zero (hp : ClPre w A T G P c R GB RB h mem) {x : ℕ}
    (hx : (SuN.z 𝔑 23 21 2 11 ≤ x ∧ x < SuN.D 𝔑) ∨ SuN.RR 𝔑 ≤ x) : a.P3 x = 0 := by
  have hnA : a.hM.nA ≤ SuN.nS 𝔑 := selL_length_le _ _ _ _ _
  have eD : SuN.D 𝔑 = SuN.z 𝔑 23 26 2 16 := rfl
  have eL : SuN.L 𝔑 = P.L := rfl
  have eR := (SuN.RR_eq' 𝔑)
  have hJ : SuN.J 𝔑 = (suVOf GB RB h mem).J := rfl
  have hs' : SuN.s 𝔑 = (suVOf GB RB h mem).s := rfl
  rw [a.u3f _ (fun h' => by unfold pqOut at h'; simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega), a.u2f _ (by simp only [SuN.z] at *; omega),
    a.u1f _ (by simp only [SuN.z] at *; omega), a.t4f _ (by simp only [SuN.z] at *; omega),
    a.t3f _ (by simp only [SuN.z] at *; omega), a.t2f _ (by simp only [SuN.z] at *; omega),
    a.t1f _ (by simp only [SuN.z] at *; omega),
    a.pg_fr _ (Or.inr (by simp only [SuN.z] at *; omega))]
  exact a.m4_zero hp (by simp only [SuN.z] at *; omega)

/-- The last cell of the copy `NXT` is zero. -/
theorem nxt_s (hp : ClPre w A T G P c R GB RB h mem) :
    a.P3 (SuN.z 𝔑 18 19 0 6 + SuN.s 𝔑) = 0 := by
  have hnA : a.hM.nA ≤ SuN.nS 𝔑 := selL_length_le _ _ _ _ _
  rw [a.fr_hi _ (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z] at *; omega) (by simp only [SuN.z] at *; omega)
    (by simp only [SuN.z, SuN.D] at *; omega),
    a.pg_fr _ (Or.inr (by simp only [SuN.z] at *; omega))]
  exact a.m4_zero hp (by simp only [SuN.z] at *; omega)

end SuAt

end MinCostFlow.LowStretch
