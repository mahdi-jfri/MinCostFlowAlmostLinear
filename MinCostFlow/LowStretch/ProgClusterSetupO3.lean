module

public import MinCostFlow.LowStretch.ProgClusterSetupTt

/-!
# The setup of a cluster: the arcs of the petal graph after the setup

The facts `classes`, `heads`, `arcsN`, `ordA` and `hsum` of `PW.Ok` for the memory `F` after the
setup. The arcs of the active entries come from `pgPC`, with the nodes and shifted lengths of
`ClPre.actEnt`. The slots have the cost and class of the parent arcs, whose cost is the cost of
their class (`SuMem.tcls`), whose class is below `J` and whose cost is at most `Δ`
(`SuMem.slot`). The arcs of the entries have classes below `J + 5` (`rcK_lt`, from the bound of
the precondition of `pgP`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

variable {w A : ℕ} {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {GB RB h : ℕ}
  {mem : ℕ → ℕ} {st : State} {a : SuAt w T G P c R GB RB h mem st} {F : ℕ → ℕ}

set_option hygiene false in
/-- The layout of the setup, as numbers. -/
local notation "𝔑" => (suVOf GB RB h mem).N P.L

set_option hygiene false in
/-- The setting of `pgP` in the setup. -/
local notation "𝔄" => suPGA (suVOf GB RB h mem) P.L a.hM.nA

theorem ClPre.J_pos (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) :
    1 ≤ (GlobL.read mem GB).J := by
  have hJ0 : 128 * P.B * G.n ^ 2 < 2 ^ (GlobL.read mem GB).J := hp.glob.hJ
  have hB1 : 1 ≤ P.B := hp.ok.hB
  have hn1 : 1 ≤ G.n := hp.ok.n_pos hX
  by_contra h0
  have e : (GlobL.read mem GB).J = 0 := by omega
  rw [e, pow_zero] at hJ0
  have : 0 < P.B * G.n ^ 2 := Nat.mul_pos (by omega) (pow_pos (by omega) 2)
  have e2 : 128 * P.B * G.n ^ 2 = 128 * (P.B * G.n ^ 2) := by ring
  omega

/-- **The slots**: the cost of the slot of `u` is the cost of its class, its class is below `J`
and its cost is at most `Δ`. -/
theorem SuAt.slot_cls (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) {u : ℕ}
    (hu : u < SuN.s 𝔑) :
    (𝔄).toSF.sc a.M4 u = cofK (RecL.read mem RB).lθ ((𝔄).toSF.sk a.M4 u) ∧
      (𝔄).toSF.sk a.M4 u < (GlobL.read mem GB).J ∧ (𝔄).toSF.sc a.M4 u ≤ c.Δ G := by
  have hJ1 := hp.J_pos hX
  unfold SF.sc SF.sk
  split_ifs with hx
  · exact ⟨by simp [cofK], hJ1, Nat.zero_le _⟩
  · have hu' : u < (RecL.read mem RB).s := hu
    have e1 : (𝔄).toSF.PC + u = SuN.Z 𝔑 + 7 * (RecL.read mem RB).s + 1 + u := by
      show SuN.z 𝔑 0 7 0 1 + u = _; simp only [SuN.z, Nat.zero_mul, Nat.add_zero]; rfl
    have e2 : (𝔄).toSF.CS1 + u = SuN.Z 𝔑 + 5 * (RecL.read mem RB).s + 1 + u := by
      show SuN.z 𝔑 0 5 0 1 + u = _; simp only [SuN.z, Nat.zero_mul, Nat.add_zero]; rfl
    have e3 : (𝔄).toSF.CL1 + u = SuN.Z 𝔑 + 6 * (RecL.read mem RB).s + 1 + u := by
      show SuN.z 𝔑 0 6 0 1 + u = _; simp only [SuN.z, Nat.zero_mul, Nat.add_zero]; rfl
    rw [e1, a.hM.pci hp hu', e2, e3]
    obtain ⟨s1, s2⟩ := a.hM.slot hp hX hu'
    exact ⟨a.hM.tcls hp hX hu', s1, s2⟩

namespace SuFin

variable (hf : SuFin a F) (hp : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card)
include hf hp hX

omit hf in
/-- Every arc of the graph: its cost is the cost of its class, its class is below `J + 5`
and its cost is at most `2^(lθ + J + 3) + Δ`. -/
theorem arc {k : ℕ} (hk : k < 2 * a.hM.nA + SuN.s 𝔑) :
    a.M5 (SuN.z 𝔑 14 16 0 5 + k) = cofK (RecL.read mem RB).lθ (a.M5 (SuN.z 𝔑 16 17 0 5 + k)) ∧
      a.M5 (SuN.z 𝔑 16 17 0 5 + k) < (GlobL.read mem GB).J + 5 ∧
      a.M5 (SuN.z 𝔑 14 16 0 5 + k) ≤ 2 ^ ((RecL.read mem RB).lθ + ((GlobL.read mem GB).J + 3)) +
        c.Δ G := by
  have hpre := hp.pgPre hX a.hM
  have hJ1 : 1 ≤ (𝔄).Jc := by show 1 ≤ (GlobL.read mem GB).J + 3; omega
  rcases (a.suPg.heads k hk).2 with ⟨j, hj, h1 | h1⟩ | ⟨u, hu, h1, h2⟩
  · have hk1 : (𝔄).toPF.k1 a.M4 j < (𝔄).Jc + 2 := rcK_lt (hpre.fill.x1_le j hj) hJ1
    have hc := cofK_le (lθ := (𝔄).lθ) hk1 hJ1
    rw [h1.1, h1.2]
    exact ⟨rfl, hk1, le_trans hc (Nat.le_add_right _ _)⟩
  · have hk1 : (𝔄).toPF.k2 a.M4 j < (𝔄).Jc + 2 := rcK_lt (hpre.fill.x2_le j hj) hJ1
    have hc := cofK_le (lθ := (𝔄).lθ) hk1 hJ1
    rw [h1.1, h1.2]
    exact ⟨rfl, hk1, le_trans hc (Nat.le_add_right _ _)⟩
  · obtain ⟨s1, s2, s3⟩ := a.slot_cls hp hX hu
    rw [h1, h2]
    exact ⟨s1, by omega, le_trans s3 (Nat.le_add_left _ _)⟩

theorem classes : ∀ k < a.W.L.MM, ∀ k' < a.W.L.MM, F (a.W.L.CL + k) = F (a.W.L.CL + k') →
    F (a.W.L.CS + k) = F (a.W.L.CS + k') := by
  have := SuAt.nA_le (a := a)
  refine PGA.classes (lθ := (RecL.read mem RB).lθ) fun k hk => ?_
  have hk' : k < 2 * a.hM.nA + SuN.s 𝔑 := hk
  show F (SuN.z 𝔑 14 16 0 5 + k) = cofK _ (F (SuN.z 𝔑 16 17 0 5 + k))
  rw [hf.cs (by omega), hf.cl (by omega)]
  exact (SuFin.arc (a := a) hp hX hk').1

theorem heads
    (hw : (GlobL.read mem GB).INF + (2 ^ ((RecL.read mem RB).lθ + ((GlobL.read mem GB).J + 3)) +
      c.Δ G) < 2 ^ w) :
    ∀ k < a.W.L.MM, F (a.W.L.CL + k) < a.W.L.J ∧ a.W.L.INF + F (a.W.L.CS + k) < 2 ^ w := by
  have := SuAt.nA_le (a := a)
  intro k hk
  have hk' : k < 2 * a.hM.nA + SuN.s 𝔑 := hk
  show F (SuN.z 𝔑 16 17 0 5 + k) < (GlobL.read mem GB).J + 5 ∧
    (GlobL.read mem GB).INF + F (SuN.z 𝔑 14 16 0 5 + k) < 2 ^ w
  rw [hf.cs (by omega), hf.cl (by omega)]
  obtain ⟨-, e2, e3⟩ := SuFin.arc (a := a) hp hX hk'
  exact ⟨e2, by omega⟩

omit hf hX in
/-- The nodes and shifted lengths of the active entries, for `PW.Ok.arcsN`. -/
theorem ent_eq {j : ℕ} (hj : j < a.hM.nA) :
    (𝔄).toPF.ea a.M4 j = a.W.ea j ∧ (𝔄).toPF.eb a.M4 j = a.W.eb j ∧
      (𝔄).toPF.x1 a.M4 j = a.W.c.wbar a.W.G (a.W.pr j) (a.W.G.pu (a.W.pr j))
        (a.W.G.pv (a.W.pr j)) ∧
      (𝔄).toPF.x2 a.M4 j = a.W.c.wbar a.W.G (a.W.pr j) (a.W.G.pv (a.W.pr j))
        (a.W.G.pu (a.W.pr j)) := by
  obtain ⟨e, -⟩ := hp.actEnt a.hM hj
  exact ⟨e.ea, e.eb, e.x1, e.x2⟩

omit hX in
/-- The arcs of a node before its slot (`PW.Ok.arcsN`). -/
theorem arcsN : ∀ u < a.W.s, ∀ Q : ℕ → ℕ → Prop,
    (∃ k, F (a.W.L.LO + u) ≤ k ∧ k + 1 < F (a.W.L.HI + u) ∧
      Q (F (a.W.L.HD + k)) (F (a.W.L.CS + k))) ↔
      ∃ j < a.W.nA,
        (a.W.ea j = u ∧ Q (a.W.eb j) (rc a.W.c.θ (a.W.c.wbar a.W.G (a.W.pr j)
          (a.W.G.pu (a.W.pr j)) (a.W.G.pv (a.W.pr j))))) ∨
        (a.W.eb j = u ∧ Q (a.W.ea j) (rc a.W.c.θ (a.W.c.wbar a.W.G (a.W.pr j)
          (a.W.G.pv (a.W.pr j)) (a.W.G.pu (a.W.pr j))))) := by
  rw [SuAt.W_s hp]
  intro u hu Q
  have := SuAt.nA_le (a := a)
  have tr : (∃ k, F (a.W.L.LO + u) ≤ k ∧ k + 1 < F (a.W.L.HI + u) ∧
      Q (F (a.W.L.HD + k)) (F (a.W.L.CS + k))) ↔
      (∃ k, a.M5 ((𝔄).OFF + u) ≤ k ∧ k + 1 < a.M5 ((𝔄).OFF + 1 + u) ∧
        Q (a.M5 ((𝔄).HD + k)) (a.M5 ((𝔄).CS + k))) := by
    show (∃ k, F (SuN.z 𝔑 10 12 0 2 + u) ≤ k ∧ k + 1 < F (SuN.z 𝔑 10 12 0 3 + u) ∧
      Q (F (SuN.z 𝔑 12 15 0 5 + k)) (F (SuN.z 𝔑 14 16 0 5 + k))) ↔
      (∃ k, a.M5 (SuN.z 𝔑 10 12 0 2 + u) ≤ k ∧ k + 1 < a.M5 (SuN.z 𝔑 10 12 0 2 + 1 + u) ∧
        Q (a.M5 (SuN.z 𝔑 12 15 0 5 + k)) (a.M5 (SuN.z 𝔑 14 16 0 5 + k)))
    rw [hf.off (by omega), hf.hi (by omega)]
    refine exists_congr fun k => and_congr_right fun _ => and_congr_right fun h2 => ?_
    have := SuFin.hi_le (a := a) (u := u) (by omega)
    rw [hf.hd (by omega), hf.cs (by omega)]
  rw [tr]
  have hθ : a.W.c.θ = 2 ^ (𝔄).lθ := hp.recAt.arcs.th
  exact PGA.arcsN (A := 𝔄) (mem := a.M4) (mem' := a.M5) (pr := a.W.pr) a.suPg.arcs rfl rfl rfl rfl rfl rfl rfl
    hθ (fun j hj => (SuFin.ent_eq (a := a) hp hj).1) (fun j hj => (SuFin.ent_eq (a := a) hp hj).2.1)
    (fun j hj => (SuFin.ent_eq (a := a) hp hj).2.2.1) (fun j hj => (SuFin.ent_eq (a := a) hp hj).2.2.2) u hu Q

omit hX in
/-- The sums over the arcs of a node (`PW.Ok.hsum`). -/
theorem hsum : ∀ u < a.W.s, ∀ Fs : ℕ → ℕ → ℕ,
    ∑ k ∈ Finset.Ico (F (a.W.L.LO + u)) (F (a.W.L.HI + u) - 1),
        Fs (F (a.W.L.HD + k)) (F (a.W.ORD + k) / 2) =
      ∑ j ∈ (Finset.range a.W.nA).filter (a.W.ea · = u), Fs (a.W.eb j) j +
      ∑ j ∈ (Finset.range a.W.nA).filter (a.W.eb · = u), Fs (a.W.ea j) j := by
  rw [SuAt.W_s hp]
  intro u hu Fs
  have := SuAt.nA_le (a := a)
  have hle := SuFin.hi_le (a := a) (u := u) (by omega)
  show ∑ k ∈ Finset.Ico (F (SuN.z 𝔑 10 12 0 2 + u)) (F (SuN.z 𝔑 10 12 0 3 + u) - 1),
      Fs (F (SuN.z 𝔑 12 15 0 5 + k)) (F (SuN.z 𝔑 18 20 0 7 + k) / 2) = _
  rw [hf.off (by omega), hf.hi (by omega)]
  have e : ∀ k ∈ Finset.Ico (a.M5 (SuN.z 𝔑 10 12 0 2 + u))
      (a.M5 (SuN.z 𝔑 10 12 0 2 + 1 + u) - 1),
      Fs (F (SuN.z 𝔑 12 15 0 5 + k)) (F (SuN.z 𝔑 18 20 0 7 + k) / 2) =
        Fs (a.M5 (SuN.z 𝔑 12 15 0 5 + k)) (a.M5 (SuN.z 𝔑 10 14 0 5 + k) / 2) := by
    intro k hk
    have := (Finset.mem_Ico.mp hk).2
    rw [hf.hd (by omega), hf.ordc (by omega)]
  rw [Finset.sum_congr rfl e, a.suPg.sum u hu Fs]
  have f1 : (Finset.range a.hM.nA).filter ((𝔄).toPF.ea a.M4 · = u) =
      (Finset.range a.W.nA).filter (a.W.ea · = u) :=
    Finset.filter_congr fun j hj => by rw [(SuFin.ent_eq (a := a) hp (Finset.mem_range.mp hj)).1]
  have f2 : (Finset.range a.hM.nA).filter ((𝔄).toPF.eb a.M4 · = u) =
      (Finset.range a.W.nA).filter (a.W.eb · = u) :=
    Finset.filter_congr fun j hj => by rw [(SuFin.ent_eq (a := a) hp (Finset.mem_range.mp hj)).2.1]
  rw [f1, f2]
  congr 1
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [(SuFin.ent_eq (a := a) hp (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)).2.1]
  · refine Finset.sum_congr rfl fun j hj => ?_
    rw [(SuFin.ent_eq (a := a) hp (Finset.mem_range.mp (Finset.mem_filter.mp hj).1)).1]

omit hX in
/-- The arcs before the slot come from entries below `nA` (`PW.Ok.ordA`). -/
theorem ordA : ∀ u < a.W.s, ∀ k, F (a.W.L.LO + u) ≤ k → k < F (a.W.L.HI + u) - 1 →
    F (a.W.ORD + k) / 2 < a.W.nA :=
  PGA.ordA (hf.hsum hp)

end SuFin

end MinCostFlow.LowStretch
