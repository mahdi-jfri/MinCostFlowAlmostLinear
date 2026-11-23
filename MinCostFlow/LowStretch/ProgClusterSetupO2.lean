module

public import MinCostFlow.LowStretch.ProgClusterSetupO1

/-!
# The setup of a cluster: the ranges of the petal graph after the setup

The graph of `pgP` lies in the cells `TL … OK + s`, which no later step writes. So the facts
of `pgPC` about the ranges `OFF`, the heads `HD`, the costs `CS`, the classes `CL` and the marks
`OK` hold in the memory `F` after the setup (`SuFin.off`, `SuFin.hi`, …). From them we get the
facts `sS`, `lohi`, `chain`, `hiMM`, `hdNN`, `hdN` and `budget` of `PW.Ok`, and the slots
`Btw.sl` (all slots off).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st} {F : ℕ → ℕ}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

theorem SuAt.W_s (hp : ClPre w A T G P c R GB RB h mem) : a.W.s = SuN.s 𝔑 :=
  hp.recAt.arcs.s.symm

theorem SuAt.nA_le : a.hM.nA ≤ SuN.nS 𝔑 := selL_length_le _ _ _ _ _

/-- The facts of `pgPC` for the setting of the setup, at the addresses of the layout. -/
structure SuPg (s nA : ℕ) (N : SuN) (M4 M5 : ℕ → ℕ) (A : PGA) : Prop where
  o0 : M5 (N.z 10 12 0 2) = 0
  mono : ∀ u < s + 1, M5 (N.z 10 12 0 2 + u) ≤ M5 (N.z 10 12 0 2 + 1 + u)
  last : M5 (N.z 10 12 0 2 + s) = 2 * nA + s
  last1 : M5 (N.z 10 12 0 2 + 1 + s) = 2 * nA + s
  slot : ∀ u < s, M5 (N.z 10 12 0 2 + u) < M5 (N.z 10 12 0 2 + 1 + u) ∧
      M5 (N.z 12 15 0 5 + (M5 (N.z 10 12 0 2 + 1 + u) - 1)) = s ∧
      M5 (N.z 14 16 0 5 + (M5 (N.z 10 12 0 2 + 1 + u) - 1)) = A.toSF.sc M4 u ∧
      M5 (N.z 16 17 0 5 + (M5 (N.z 10 12 0 2 + 1 + u) - 1)) = A.toSF.sk M4 u
  arcs : ∀ u < s, ∀ P : ℕ → ℕ → ℕ → Prop,
      (∃ k, M5 (N.z 10 12 0 2 + u) ≤ k ∧ k + 1 < M5 (N.z 10 12 0 2 + 1 + u) ∧
        P (M5 (N.z 12 15 0 5 + k)) (M5 (N.z 14 16 0 5 + k)) (M5 (N.z 16 17 0 5 + k))) ↔
      ∃ j < nA,
        (A.toPF.ea M4 j = u ∧ P (A.toPF.eb M4 j) (cofK A.lθ (A.toPF.k1 M4 j)) (A.toPF.k1 M4 j)) ∨
        (A.toPF.eb M4 j = u ∧ P (A.toPF.ea M4 j) (cofK A.lθ (A.toPF.k2 M4 j)) (A.toPF.k2 M4 j))
  heads : ∀ k < 2 * nA + s, M5 (N.z 12 15 0 5 + k) < s + 1 ∧
      ((∃ j < nA, (M5 (N.z 14 16 0 5 + k) = cofK A.lθ (A.toPF.k1 M4 j) ∧
          M5 (N.z 16 17 0 5 + k) = A.toPF.k1 M4 j) ∨
        (M5 (N.z 14 16 0 5 + k) = cofK A.lθ (A.toPF.k2 M4 j) ∧
          M5 (N.z 16 17 0 5 + k) = A.toPF.k2 M4 j)) ∨
       ∃ u < s, M5 (N.z 14 16 0 5 + k) = A.toSF.sc M4 u ∧
         M5 (N.z 16 17 0 5 + k) = A.toSF.sk M4 u)
  ok : ∀ v < s, M5 (N.z 18 18 0 5 + v) = 0
  ok_s : M5 (N.z 18 18 0 5 + s) = 1
  sum : ∀ u < s, ∀ Fs : ℕ → ℕ → ℕ,
      ∑ k ∈ Finset.Ico (M5 (N.z 10 12 0 2 + u)) (M5 (N.z 10 12 0 2 + 1 + u) - 1),
          Fs (M5 (N.z 12 15 0 5 + k)) (M5 (N.z 10 14 0 5 + k) / 2) =
        ∑ j ∈ (Finset.range nA).filter (A.toPF.ea M4 · = u), Fs (A.toPF.eb M4 j) j +
        ∑ j ∈ (Finset.range nA).filter (A.toPF.eb M4 · = u), Fs (A.toPF.ea M4 j) j

theorem SuAt.suPg (a : SuAt w T G P c R GB RB h mem st) :
    SuPg (SuN.s 𝔑) a.hM.nA 𝔑 a.M4 a.M5 (suPGA (suVOf GB RB h mem) P.L a.hM.nA) := by
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, -, p10⟩ := a.pg _ rfl
  exact ⟨p0, p1, p2, p3, p4, p5, p6, p7, p8, p10⟩

namespace SuFin

variable (hf : SuFin a F)
include hf

theorem off {u : ℕ} (hu : u ≤ SuN.s 𝔑 + 1) :
    F (SuN.z 𝔑 10 12 0 2 + u) = a.M5 (SuN.z 𝔑 10 12 0 2 + u) :=
  hf.pgc (by simp only [SuN.z]; omega) (by simp only [SuN.z]; omega)

theorem hi {u : ℕ} (hu : u ≤ SuN.s 𝔑) :
    F (SuN.z 𝔑 10 12 0 3 + u) = a.M5 (SuN.z 𝔑 10 12 0 2 + 1 + u) := by
  rw [show SuN.z 𝔑 10 12 0 3 + u = SuN.z 𝔑 10 12 0 2 + 1 + u by simp only [SuN.z]]
  exact hf.pgc (by simp only [SuN.z]; omega) (by simp only [SuN.z]; omega)

theorem hd {k : ℕ} (hk : k < 2 * SuN.nS 𝔑 + SuN.s 𝔑) :
    F (SuN.z 𝔑 12 15 0 5 + k) = a.M5 (SuN.z 𝔑 12 15 0 5 + k) :=
  hf.pgc (by simp only [SuN.z]; omega) (by simp only [SuN.z]; omega)

theorem cs {k : ℕ} (hk : k < 2 * SuN.nS 𝔑 + SuN.s 𝔑) :
    F (SuN.z 𝔑 14 16 0 5 + k) = a.M5 (SuN.z 𝔑 14 16 0 5 + k) :=
  hf.pgc (by simp only [SuN.z]; omega) (by simp only [SuN.z]; omega)

theorem cl {k : ℕ} (hk : k < 2 * SuN.nS 𝔑 + SuN.s 𝔑) :
    F (SuN.z 𝔑 16 17 0 5 + k) = a.M5 (SuN.z 𝔑 16 17 0 5 + k) :=
  hf.pgc (by simp only [SuN.z]; omega) (by simp only [SuN.z]; omega)

theorem okc {v : ℕ} (hv : v ≤ SuN.s 𝔑) :
    F (SuN.z 𝔑 18 18 0 5 + v) = a.M5 (SuN.z 𝔑 18 18 0 5 + v) :=
  hf.pgc (by simp only [SuN.z]; omega) (by simp only [SuN.z]; omega)

omit hf in
/-- The ranges end by `MM = 2 nA + s`. -/
theorem hi_le {u : ℕ} (hu : u ≤ SuN.s 𝔑) :
    a.M5 (SuN.z 𝔑 10 12 0 2 + 1 + u) ≤ 2 * a.hM.nA + SuN.s 𝔑 := by
  have hP := a.suPg
  rcases PGA.hi_le hP.mono hP.last u (by omega) with h1 | h1
  · exact h1
  · subst h1; rw [hP.last1]

omit hf in
/-- The slot of node `u` is a cell of the graph. -/
theorem slot_lt {u : ℕ} (hu : u < SuN.s 𝔑) :
    a.M5 (SuN.z 𝔑 10 12 0 2 + 1 + u) - 1 < 2 * SuN.nS 𝔑 + SuN.s 𝔑 := by
  have := hi_le (a := a) hu.le
  have := SuAt.nA_le (a := a)
  omega

variable (hp : ClPre w A T G P c R GB RB h mem)
include hp

theorem sS : F (a.W.L.OK + a.W.s) ≠ a.W.L.os := by
  rw [SuAt.W_s hp]
  show F (SuN.z 𝔑 18 18 0 5 + SuN.s 𝔑) ≠ 0
  rw [hf.okc le_rfl, a.suPg.ok_s]; omega

theorem lohi : ∀ u < a.W.s, F (a.W.L.LO + u) < F (a.W.L.HI + u) := by
  rw [SuAt.W_s hp]
  intro u hu
  show F (SuN.z 𝔑 10 12 0 2 + u) < F (SuN.z 𝔑 10 12 0 3 + u)
  rw [hf.off (by omega), hf.hi (by omega)]
  exact (a.suPg.slot u hu).1

omit hf hp in
theorem chain : ∀ u < a.W.s, F (a.W.L.HI + u) = F (a.W.L.LO + (u + 1)) := by
  intro u _
  show F (SuN.z 𝔑 10 12 0 3 + u) = F (SuN.z 𝔑 10 12 0 2 + (u + 1))
  rw [show SuN.z 𝔑 10 12 0 3 + u = SuN.z 𝔑 10 12 0 2 + (u + 1) by simp only [SuN.z]; omega]

omit hp in
theorem hiMM : ∀ v < a.W.L.NN, F (a.W.L.HI + v) ≤ a.W.L.MM := by
  intro v hv
  have hv' : v ≤ SuN.s 𝔑 := by
    have : a.W.L.NN = SuN.s 𝔑 + 1 := rfl
    omega
  show F (SuN.z 𝔑 10 12 0 3 + v) ≤ 2 * a.hM.nA + SuN.s 𝔑
  rw [hf.hi hv']; exact hi_le (a := a) hv'

omit hp in
theorem hdNN : ∀ k < a.W.L.MM, F (a.W.L.HD + k) < a.W.L.NN := by
  intro k hk
  have hk' : k < 2 * a.hM.nA + SuN.s 𝔑 := hk
  have := SuAt.nA_le (a := a)
  show F (SuN.z 𝔑 12 15 0 5 + k) < SuN.s 𝔑 + 1
  rw [hf.hd (by omega)]
  exact (a.suPg.heads k hk').1

theorem hdN : ∀ u < a.W.s, ∀ k, F (a.W.L.LO + u) ≤ k → k + 1 < F (a.W.L.HI + u) →
    F (a.W.L.HD + k) < a.W.L.NN := by
  rw [SuAt.W_s hp]
  intro u hu k _ h2
  refine hf.hdNN k ?_
  have := hf.hiMM u (show u < a.W.L.NN by show u < SuN.s 𝔑 + 1; omega)
  omega

theorem budget (hA : 2 * a.hM.nA + 2 * SuN.s 𝔑 ≤ a.W.L.A) :
    ∑ u ∈ Finset.range a.W.s, (F (a.W.L.HI + u) - F (a.W.L.LO + u) + 1) ≤ a.W.L.A := by
  rw [SuAt.W_s hp]
  have e : ∀ u ∈ Finset.range (SuN.s 𝔑), F (a.W.L.HI + u) - F (a.W.L.LO + u) + 1 =
      a.M5 (SuN.z 𝔑 10 12 0 2 + 1 + u) - a.M5 (SuN.z 𝔑 10 12 0 2 + u) + 1 := by
    intro u hu
    have hu' := Finset.mem_range.mp hu
    show F (SuN.z 𝔑 10 12 0 3 + u) - F (SuN.z 𝔑 10 12 0 2 + u) + 1 = _
    rw [hf.hi (by omega), hf.off (by omega)]
  rw [Finset.sum_congr rfl e]
  have hP := a.suPg
  exact PGA.budget hP.mono hP.o0 hP.last hA

/-- **All slots are off** after the setup: the head of the slot of every node is `s`. -/
theorem sl : ∀ u < a.W.s, F (a.W.L.HD + a.W.slotA F u) = a.W.s := by
  rw [SuAt.W_s hp]
  intro u hu
  show F (SuN.z 𝔑 12 15 0 5 + (F (SuN.z 𝔑 10 12 0 3 + u) - 1)) = SuN.s 𝔑
  rw [hf.hi (by omega), hf.hd (slot_lt (a := a) hu)]
  exact (a.suPg.slot u hu).2.1

end SuFin

end MinCostFlow.LowStretch
