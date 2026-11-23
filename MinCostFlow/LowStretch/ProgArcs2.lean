module

public import MinCostFlow.LowStretch.ProgArcs
public import MinCostFlow.LowStretch.DijAbs

/-!
# The arc graph of a cluster

`arcP` runs `arcFill`, groups the items by their tails with `csrB`, and copies them in that order
with `arcCopy`. The arcs of local node `u` are then the cells `OFF[u], …, OFF[u + 1] - 1` of the
arrays `HD` (heads) and `CS` (costs). So the arcs from `u` to `v` of cost `c` are the two
directions of the kept stored pairs between `u` and `v` of length `c` (`arcP_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

section csr

variable (f : ℕ → ℕ)

theorem offOf_le (M u : ℕ) : offOf f M u ≤ M := by
  unfold offOf
  exact (List.length_filter_le _ _).trans (by simp)

/-- **The cells of a key are its items.** -/
theorem csr_exists_iff {M u : ℕ} {ord : ℕ → ℕ}
    (hord : ∀ j < (grp f M u).length, ord (offOf f M u + j) = (grp f M u).getD j 0)
    (P : ℕ → Prop) :
    (∃ k, offOf f M u ≤ k ∧ k < offOf f M (u + 1) ∧ P (ord k)) ↔ ∃ i < M, f i = u ∧ P i := by
  rw [offOf_succ]
  constructor
  · rintro ⟨k, hk1, hk2, hP⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = offOf f M u + j := ⟨k - offOf f M u, by omega⟩
    have hj : j < (grp f M u).length := by omega
    rw [hord j hj] at hP
    have hmem : (grp f M u).getD j 0 ∈ grp f M u := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    unfold grp at hmem
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hmem
    exact ⟨_, hmem.1, hmem.2, hP⟩
  · rintro ⟨i, hi, hfi, hP⟩
    have hmem : i ∈ grp f M u := by
      unfold grp; simp [hi, hfi]
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.mp hmem
    refine ⟨offOf f M u + j, by omega, by omega, ?_⟩
    rw [hord j hj, List.getD_eq_getElem _ _ hj, hji]
    exact hP


/-- Every cell below `M` lies in the range of some key below `NN`. -/
theorem exists_bucket {M NN : ℕ} (hall : ∀ i < M, f i < NN) {j : ℕ} (hj : j < M) :
    ∃ u < NN, offOf f M u ≤ j ∧ j < offOf f M (u + 1) := by
  classical
  have hN : offOf f M NN = M := offOf_all f hall
  have hex : ∃ u, j < offOf f M (u + 1) := ⟨NN, by
    have := offOf_mono f (M := M) (show NN ≤ NN + 1 by omega); omega⟩
  let u := Nat.find hex
  have hu : j < offOf f M (u + 1) := Nat.find_spec hex
  have hle : offOf f M u ≤ j := by
    rcases Nat.eq_zero_or_pos u with h0 | hpos
    · rw [h0, offOf_zero]; exact Nat.zero_le _
    · have := Nat.find_min hex (show u - 1 < u by omega)
      rw [show u - 1 + 1 = u by omega] at this
      omega
  refine ⟨u, ?_, hle, hu⟩
  by_contra hc
  have := offOf_mono f (M := M) (show NN ≤ u by omega)
  omega

/-- The item stored at a cell is an item of the key of that cell. -/
theorem csr_item {M NN : ℕ} {ord : ℕ → ℕ} (hall : ∀ i < M, f i < NN)
    (hord : ∀ u < NN, ∀ j < (grp f M u).length, ord (offOf f M u + j) = (grp f M u).getD j 0)
    {k : ℕ} (hk : k < M) : ord k < M := by
  obtain ⟨u, hu, h1, h2⟩ := exists_bucket f hall hk
  obtain ⟨i, hi, -, hP⟩ := (csr_exists_iff f (hord u hu) (fun i => ord k = i)).mp
    ⟨k, h1, h2, rfl⟩
  rw [hP]; exact hi

end csr

/-- The addresses and numbers that `arcP` uses. -/
structure AP where
  s : ℕ
  nS : ℕ
  SA : ℕ
  IN : ℕ
  PW : ℕ
  EXP : ℕ
  LAB : ℕ
  LOC : ℕ
  D : ℕ
  lθ : ℕ
  TL : ℕ
  HDt : ℕ
  CSt : ℕ
  CLt : ℕ
  OFF : ℕ
  CNT : ℕ
  ORD : ℕ
  HD : ℕ
  CS : ℕ
  CL : ℕ
  OK : ℕ
  os : ℕ

namespace AP

variable (A : AP)

def args : List ℕ :=
  [A.s, A.nS, A.SA, A.IN, A.PW, A.EXP, A.LAB, A.LOC, A.D, A.lθ, A.TL, A.HDt, A.CSt, A.CLt,
    A.OFF, A.CNT, A.ORD, A.HD, A.CS, A.CL, A.OK, A.os]

theorem eq_of_args {A A' : AP} (h : A.args = A'.args) : A' = A := by
  cases A; cases A'; simp only [AP.args, List.cons.injEq] at h
  simp_all

def toAF : AF := ⟨A.s, A.nS, A.SA, A.IN, A.PW, A.EXP, A.LAB, A.LOC, A.D, A.lθ, A.TL, A.HDt,
  A.CSt, A.CLt⟩

def toAC : AC := ⟨2 * A.nS, A.ORD, A.HDt, A.CSt, A.CLt, A.HD, A.CS, A.CL, A.OK, A.s, A.os⟩

/-- The arc graph in memory: node `u ≤ s` has the arcs `OFF[u], …, OFF[u + 1] - 1`, and the
allowed heads are the nodes `v < s` marked `os`. -/
def g (mem : ℕ → ℕ) : AG where
  lo u := if u < A.s + 1 then mem (A.OFF + u) else 0
  hi u := if u < A.s + 1 then mem (A.OFF + 1 + u) else 0
  hd k := if k < 2 * A.nS then mem (A.HD + k) else 0
  cs k := if k < 2 * A.nS then mem (A.CS + k) else 0
  ok v := v < A.s + 1 ∧ mem (A.OK + v) = A.os

/-- The precondition of `arcP`. -/
structure Pre (w : ℕ) (mem : ℕ → ℕ) (m n NL : ℕ) : Prop where
  fill : A.toAF.Pre w mem m n NL
  ea_lt : ∀ j < A.nS, A.toAF.ea mem j < A.s
  eb_lt : ∀ j < A.nS, A.toAF.eb mem j < A.s
  l5 : A.CLt + 2 * A.nS ≤ A.OFF
  l6 : A.OFF + (A.s + 1) + 1 ≤ A.CNT
  l7 : A.CNT + (A.s + 1) ≤ A.ORD
  l8 : A.ORD + 2 * A.nS ≤ A.HD
  l9 : A.HD + 2 * A.nS ≤ A.CS
  l10 : A.CS + 2 * A.nS ≤ A.CL
  l11 : A.CL + 2 * A.nS ≤ A.OK
  l12 : A.OK + A.s + 3 < 2 ^ w
  los : A.os + 1 < 2 ^ w
  rSA' : A.SA + 2 * A.nS ≤ A.TL ∨ A.OK + A.s < A.SA

end AP

/-- `arcP bF bC bY` with `args = A.args`; `arcFill`, `csrB` and `arcCopy` sit at `bF`, `bC` and
`bY`. -/
def arcP (bF bC bY : ℕ) : Stmt :=
  .seq (.call 22 bF [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8, .reg 9,
    .reg 10, .reg 11, .reg 12, .reg 13])
  (.seq (.call 22 bC [.reg 10, .bin .mul (.const 2) (.reg 1), .bin .add (.reg 0) (.const 1),
    .reg 14, .reg 15, .reg 16])
  (.seq (.call 22 bY [.bin .mul (.const 2) (.reg 1), .reg 16, .reg 11, .reg 12, .reg 13,
    .reg 17, .reg 18, .reg 19, .reg 20, .reg 0, .reg 21])
  (.ret (.const 0))))

theorem arcP_noRand (bF bC bY : ℕ) : (arcP bF bC bY).NoRand := by simp [arcP, Stmt.NoRand]

/-- The contract of `arcP`. -/
def arcPC (w : ℕ) : Contract where
  pre args mem := ∃ A : AP, ∃ m n NL, args = A.args ∧ A.Pre w mem m n NL
  post args mem _ mem' := ∀ A : AP, args = A.args →
    (∀ u v c, (A.g mem').Arc u v c ↔ ∃ j < A.nS, A.toAF.keep mem j ∧
      ((A.toAF.ea mem j = u ∧ A.toAF.eb mem j = v) ∨ (A.toAF.eb mem j = u ∧ A.toAF.ea mem j = v)) ∧
      A.toAF.ln mem j = c) ∧
    (∀ k < 2 * A.nS, ∃ j < A.nS,
      (mem' (A.HD + k) = A.toAF.ta mem j ∨ mem' (A.HD + k) = A.toAF.tb mem j) ∧
      mem' (A.CS + k) = A.toAF.cs mem j ∧ mem' (A.CL + k) = A.toAF.cc mem j) ∧
    mem' A.OFF = 0 ∧ (∀ u < A.s + 1, mem' (A.OFF + u) ≤ mem' (A.OFF + 1 + u)) ∧
    mem' (A.OFF + 1 + A.s) = 2 * A.nS ∧
    (∀ v < A.s, mem' (A.OK + v) = A.os) ∧ mem' (A.OK + A.s) = A.os + 1 ∧
    (∀ u < A.s, ∀ k, mem' (A.OFF + u) ≤ k → k < mem' (A.OFF + 1 + u) →
      mem' (A.ORD + k) / 2 < A.nS ∧ A.toAF.keep mem (mem' (A.ORD + k) / 2) ∧
      ((A.toAF.ea mem (mem' (A.ORD + k) / 2) = u ∧
          mem' (A.HD + k) = A.toAF.eb mem (mem' (A.ORD + k) / 2)) ∨
        (A.toAF.eb mem (mem' (A.ORD + k) / 2) = u ∧
          mem' (A.HD + k) = A.toAF.ea mem (mem' (A.ORD + k) / 2))) ∧
      mem' (A.CS + k) = A.toAF.ln mem (mem' (A.ORD + k) / 2) ∧
      mem' (A.CL + k) = A.toAF.cl mem (mem' (A.ORD + k) / 2)) ∧
    ∀ a, ¬ (A.TL ≤ a ∧ a ≤ A.OK + A.s) → mem' a = mem a
  cost args _ := 700 * (args.getD 1 0 + args.getD 0 0) + 500

theorem arcP_spec {w : ℕ} {p : Program} {b bF bC bY : ℕ} (hp : p.HasAt b [arcP bF bC bY])
    (hF : p.HasAt bF [arcFill]) (hC : p.HasAt bC [csrB]) (hY : p.HasAt bY [arcCopy]) :
    MeetsContract w p b (arcPC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨A, m, n, NL, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some (arcP bF bC bY) := hp 0 (by simp)
  have sF := arcFill_spec (w := w) hF
  have sC := csrB_spec (w := w) hC
  have sY := arcCopy_spec (w := w) hY
  clear hp hF hC hY
  have hf := h.fill
  have l1 := hf.l1; have l2 := hf.l2; have l3 := hf.l3; have l4 := hf.l4
  have l5 := h.l5; have l6 := h.l6; have l7 := h.l7; have l8 := h.l8; have l9 := h.l9
  have l10 := h.l10; have l11 := h.l11; have l12 := h.l12; have los := h.los
  have hs := hf.hs
  have hea := h.ea_lt
  have heb := h.eb_lt
  have hw1 : 1 < 2 ^ w := hf.hw
  set F := A.toAF with hF
  -- the keys of the items are below `s + 1`
  have hta : ∀ j < A.nS, F.ta mem j < A.s + 1 := fun j hj => by
    unfold AF.ta; split_ifs
    · have := hea j hj; omega
    · show A.s < A.s + 1; omega
  have htb : ∀ j < A.nS, F.tb mem j < A.s + 1 := fun j hj => by
    unfold AF.tb; split_ifs
    · have := heb j hj; omega
    · show A.s < A.s + 1; omega
  refine ⟨arcP bF bC bY, hproc, ?_⟩
  dsimp only [arcP]
  refine runs_start_le ?_
  have g0 : A.args[0]?.getD 0 = A.s := rfl
  have g1 : A.args[1]?.getD 0 = A.nS := rfl
  have g2 : A.args[2]?.getD 0 = A.SA := rfl
  have g3 : A.args[3]?.getD 0 = A.IN := rfl
  have g4 : A.args[4]?.getD 0 = A.PW := rfl
  have g5 : A.args[5]?.getD 0 = A.EXP := rfl
  have g6 : A.args[6]?.getD 0 = A.LAB := rfl
  have g7 : A.args[7]?.getD 0 = A.LOC := rfl
  have g8 : A.args[8]?.getD 0 = A.D := rfl
  have g9 : A.args[9]?.getD 0 = A.lθ := rfl
  have g10 : A.args[10]?.getD 0 = A.TL := rfl
  have g11 : A.args[11]?.getD 0 = A.HDt := rfl
  have g12 : A.args[12]?.getD 0 = A.CSt := rfl
  have g13 : A.args[13]?.getD 0 = A.CLt := rfl
  have g14 : A.args[14]?.getD 0 = A.OFF := rfl
  have g15 : A.args[15]?.getD 0 = A.CNT := rfl
  have g16 : A.args[16]?.getD 0 = A.ORD := rfl
  have g17 : A.args[17]?.getD 0 = A.HD := rfl
  have g18 : A.args[18]?.getD 0 = A.CS := rfl
  have g19 : A.args[19]?.getD 0 = A.CL := rfl
  have g20 : A.args[20]?.getD 0 = A.OK := rfl
  have g21 : A.args[21]?.getD 0 = A.os := rfl
  have hwA : ∀ a ∈ A.args, a < 2 ^ w := hwords
  simp only [AP.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hwA
  wram_step
  · exact ⟨F, m, n, NL, by simp [AP.args, AF.args, hF, AP.toAF], hf⟩
  intro v1 mem1 pos1 hpost1
  obtain ⟨hD1, hfr1⟩ := hpost1 F rfl
  clear hpost1
  -- the items, entry by entry
  have hitem : ∀ i < 2 * A.nS, ∃ j < A.nS,
      (mem1 (A.TL + i) = F.ta mem j ∧ mem1 (A.HDt + i) = F.tb mem j ∨
        mem1 (A.TL + i) = F.tb mem j ∧ mem1 (A.HDt + i) = F.ta mem j) ∧
      mem1 (A.CSt + i) = F.cs mem j ∧ mem1 (A.CLt + i) = F.cc mem j := by
    intro i hi
    obtain ⟨j, hj⟩ : ∃ j, j = i / 2 := ⟨_, rfl⟩
    have eN : F.nS = A.nS := rfl
    obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hD1 j (by omega)
    refine ⟨j, by omega, ?_⟩
    rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
    · have e : i = 2 * j := by omega
      rw [e]; exact ⟨Or.inl ⟨d1, d3⟩, d5, d7⟩
    · have e : i = 2 * j + 1 := by omega
      rw [e]; exact ⟨Or.inr ⟨d2, d4⟩, d6, d8⟩
  have eF : F.TL = A.TL ∧ F.HDt = A.HDt ∧ F.CSt = A.CSt ∧ F.CLt = A.CLt ∧ F.nS = A.nS ∧
      F.s = A.s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨eF1, eF2, eF3, eF4, eF5, eF6⟩ := eF
  rw [eF1, eF2, eF5] at l1; rw [eF2, eF3, eF5] at l2; rw [eF3, eF4, eF5] at l3
  rw [eF4, eF5] at l4
  have hkey : ∀ i < 2 * A.nS, mem1 (A.TL + i) < A.s + 1 := fun i hi => by
    obtain ⟨j, hj, hc, -⟩ := hitem i hi
    rcases hc with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e]
    · exact hta j hj
    · exact htb j hj
  wram_step
  · exact ⟨A.TL, 2 * A.nS, A.s + 1, A.OFF, A.CNT, A.ORD, by simp [AP.args], hkey,
      by omega, by omega, by omega, by omega⟩
  intro v2 mem2 pos2 hpost2
  simp only [csrC, AP.args, List.getD_cons_zero, List.getD_cons_succ] at hpost2
  obtain ⟨hoff, hord, hfr2⟩ := hpost2
  set f : ℕ → ℕ := fun i => mem1 (A.TL + i) with hfdef
  have hord' : ∀ u < A.s + 1, ∀ j < (grp f (2 * A.nS) u).length,
      (fun k => mem2 (A.ORD + k)) (offOf f (2 * A.nS) u + j) = (grp f (2 * A.nS) u).getD j 0 := by
    intro u hu j hj
    simp only
    rw [← Nat.add_assoc]; exact hord u hu j hj
  have hordlt : ∀ k < 2 * A.nS, mem2 (A.ORD + k) < 2 * A.nS := fun k hk =>
    csr_item (ord := fun k => mem2 (A.ORD + k)) f hkey hord' hk
  have hm21 : ∀ a, A.TL ≤ a → a < A.OFF → mem2 a = mem1 a := fun a h1 h2 =>
    hfr2 a (by simp only [csrOut]; omega)
  have hm10 : ∀ a, ¬ (A.TL ≤ a ∧ a < A.CLt + 2 * A.nS) → mem1 a = mem a := fun a ha =>
    hfr1 a (by simp only [AF.Out, eF1, eF4, eF5]; exact ha)
  have hcsw : ∀ j < A.nS, F.cs mem j < 2 ^ w := fun j hj => by
    unfold AF.cs; split_ifs
    · unfold AF.ln
      have := hf.pw (F.pr mem j) (hf.pr_lt j hj)
      have : mem (F.PW + F.pr mem j) >>> F.fl mem j ≤ mem (F.PW + F.pr mem j) := by
        rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
      omega
    · omega
  have hccw : ∀ j < A.nS, F.cc mem j < 2 ^ w := fun j hj => by
    unfold AF.cc; split_ifs
    · unfold AF.cl
      have := hf.ex (F.pr mem j) (hf.pr_lt j hj)
      omega
    · omega
  -- the values of the items, after `csrB`
  have hv2 : ∀ i < 2 * A.nS, ∃ j < A.nS,
      (mem2 (A.TL + i) = F.ta mem j ∧ mem2 (A.HDt + i) = F.tb mem j ∨
        mem2 (A.TL + i) = F.tb mem j ∧ mem2 (A.HDt + i) = F.ta mem j) ∧
      mem2 (A.CSt + i) = F.cs mem j ∧ mem2 (A.CLt + i) = F.cc mem j := by
    intro i hi
    rw [hm21 _ (by omega) (by omega), hm21 _ (by omega) (by omega), hm21 _ (by omega) (by omega),
      hm21 _ (by omega) (by omega)]
    exact hitem i hi
  have hvw : ∀ i < 2 * A.nS, mem2 (A.HDt + i) < 2 ^ w ∧ mem2 (A.CSt + i) < 2 ^ w ∧
      mem2 (A.CLt + i) < 2 ^ w := by
    intro i hi
    obtain ⟨j, hj, hc, e3, e4⟩ := hv2 i hi
    rw [e3, e4]
    refine ⟨?_, hcsw j hj, hccw j hj⟩
    rcases hc with ⟨-, e⟩ | ⟨-, e⟩ <;> rw [e]
    · have := htb j hj; omega
    · have := hta j hj; omega
  wram_step
  · exact ⟨A.toAC, by simp [AC.args, AP.toAC],
      { ord := hordlt, vHD := fun i hi => (hvw i hi).1, vCS := fun i hi => (hvw i hi).2.1,
        vCL := fun i hi => (hvw i hi).2.2, r1 := by simp only [AP.toAC]; omega,
        r2 := by simp only [AP.toAC]; omega, r3 := by simp only [AP.toAC]; omega,
        r4 := by simp only [AP.toAC]; omega, l1 := by simp only [AP.toAC]; omega,
        l2 := by simp only [AP.toAC]; omega, l3 := by simp only [AP.toAC]; omega,
        l4 := by simp only [AP.toAC]; omega, los := by simp only [AP.toAC]; omega }⟩
  intro v3 mem3 pos3 hpost3
  obtain ⟨hD3, hmk1, hmk2, hfr3⟩ := hpost3 A.toAC (by simp [AC.args, AP.toAC])
  clear hpost3
  wram_run
  · dsimp only at hD3 hfr3 ⊢
    simp only [AP.toAC, AC.Done1, AC.Out] at hD3 hmk1 hmk2 hfr3
    have hoff3 : ∀ u ≤ A.s + 1, mem3 (A.OFF + u) = offOf f (2 * A.nS) u := fun u hu => by
      rw [hfr3 _ (by omega)]; exact hoff u hu
    have hok : ∀ v, (v < A.s + 1 ∧ mem3 (A.OK + v) = A.os) ↔ v < A.s := fun v => by
      constructor
      · rintro ⟨h1, h2⟩
        by_contra hc
        have e : v = A.s := by omega
        rw [e, hmk2] at h2; omega
      · intro hv; exact ⟨by omega, hmk1 v hv⟩
    have hhd : ∀ k < 2 * A.nS, mem3 (A.HD + k) = mem1 (A.HDt + mem2 (A.ORD + k)) ∧
        mem3 (A.CS + k) = mem1 (A.CSt + mem2 (A.ORD + k)) ∧
        mem3 (A.CL + k) = mem1 (A.CLt + mem2 (A.ORD + k)) := by
      intro k hk
      obtain ⟨e1, e2, e3⟩ := hD3 k hk
      have := hordlt k hk
      exact ⟨by rw [e1]; exact hm21 _ (by omega) (by omega),
        by rw [e2]; exact hm21 _ (by omega) (by omega),
        by rw [e3]; exact hm21 _ (by omega) (by omega)⟩
    intro A' hA'
    rw [AP.eq_of_args hA']
    refine ⟨fun u v c => ?_, fun k hk => ?_, ?_, fun u hu => ?_, ?_, hmk1, hmk2,
      fun u hu k hk1 hk2 => ?_, fun a ha => ?_⟩
    · simp only [AG.Arc, AP.g]
      by_cases hu : u < A.s + 1
      · rw [if_pos hu, if_pos hu, hoff3 u (by omega),
          show A.OFF + 1 + u = A.OFF + (u + 1) by omega, hoff3 (u + 1) (by omega)]
        simp only [hok]
        have key := csr_exists_iff (ord := fun k => mem2 (A.ORD + k)) f (hord' u hu)
          (fun i => mem1 (A.HDt + i) = v ∧ mem1 (A.CSt + i) = c ∧ v < A.s)
        have hlt : ∀ k, k < offOf f (2 * A.nS) (u + 1) → k < 2 * A.nS := fun k hk =>
          lt_of_lt_of_le hk (offOf_le f _ _)
        constructor
        · rintro ⟨k, h1, h2, h3, h4, h5⟩
          have hk := hlt k h2
          rw [if_pos hk, (hhd k hk).1] at h3
          rw [if_pos hk, (hhd k hk).2.1] at h4
          obtain ⟨i, hi, hfi, hv1, hc1, hvs⟩ := key.mp ⟨k, h1, h2, h3, h4, h5⟩
          have hfi' : mem1 (A.TL + i) = u := hfi
          obtain ⟨j, hj, hc, e3, -⟩ := hitem i hi
          refine ⟨j, hj, ?_⟩
          by_cases hkp : F.keep mem j
          · simp only [AF.ta, AF.tb, AF.cs, hkp, if_true] at hc e3
            refine ⟨hkp, ?_, e3.symm.trans hc1⟩
            rcases hc with ⟨a1, a2⟩ | ⟨a1, a2⟩
            · exact Or.inl ⟨a1.symm.trans hfi', a2.symm.trans hv1⟩
            · exact Or.inr ⟨a1.symm.trans hfi', a2.symm.trans hv1⟩
          · simp only [AF.ta, AF.tb, hkp, if_false] at hc
            rcases hc with ⟨-, a2⟩ | ⟨-, a2⟩ <;> omega
        · rintro ⟨j, hj, hkp, hc, hl⟩
          rw [← hF] at hkp hc hl
          obtain ⟨d1, d2, d3, d4, d5, d6, -, -⟩ := hD1 j (by omega)
          simp only [startState] at d1 d2 d3 d4 d5 d6
          simp only [AF.ta, AF.tb, AF.cs, hkp, if_true, eF1, eF2, eF3] at d1 d2 d3 d4 d5 d6
          have hP : ∃ i < 2 * A.nS, f i = u ∧
              (mem1 (A.HDt + i) = v ∧ mem1 (A.CSt + i) = c ∧ v < A.s) := by
            rcases hc with ⟨a1, a2⟩ | ⟨a1, a2⟩
            · have := heb j hj
              exact ⟨2 * j, by omega, by show mem1 (A.TL + 2 * j) = u; rw [d1, a1],
                by rw [d3, a2], by rw [d5, hl], by omega⟩
            · have := hea j hj
              exact ⟨2 * j + 1, by omega,
                by show mem1 (A.TL + (2 * j + 1)) = u; rw [← Nat.add_assoc, d2, a1],
                by rw [← Nat.add_assoc, d4, a2], by rw [← Nat.add_assoc, d6, hl], by omega⟩
          obtain ⟨k, h1, h2, h3, h4, h5⟩ := key.mpr hP
          have hk := hlt k h2
          exact ⟨k, h1, h2, by rw [if_pos hk, (hhd k hk).1]; exact h3,
            by rw [if_pos hk, (hhd k hk).2.1]; exact h4, h5⟩
      · rw [if_neg hu, if_neg hu]
        constructor
        · rintro ⟨k, h1, h2, -⟩; omega
        · rintro ⟨j, hj, -, hc, -⟩
          have := hea j hj; have := heb j hj
          rw [← hF] at hc
          rcases hc with ⟨a1, -⟩ | ⟨a1, -⟩ <;> omega
    · obtain ⟨e1, e2, e3⟩ := hhd k hk
      obtain ⟨j, hj, hc, c3, c4⟩ := hitem _ (hordlt k hk)
      refine ⟨j, hj, ?_, e2.trans c3, e3.trans c4⟩
      rw [e1]
      rcases hc with ⟨-, a⟩ | ⟨-, a⟩
      · exact Or.inr a
      · exact Or.inl a
    · have := hoff3 0 (by omega)
      rw [Nat.add_zero, offOf_zero] at this; exact this
    · rw [show A.OFF + 1 + u = A.OFF + (u + 1) by omega, hoff3 u (by omega),
        hoff3 (u + 1) (by omega)]
      exact offOf_mono f (by omega)
    · rw [show A.OFF + 1 + A.s = A.OFF + (A.s + 1) by omega, hoff3 _ le_rfl]
      exact offOf_all f hkey
    · rw [hoff3 u (by omega), show A.OFF + 1 + u = A.OFF + (u + 1) by omega,
        hoff3 (u + 1) (by omega)] at *
      have hk : k < 2 * A.nS := lt_of_lt_of_le hk2 (offOf_le f _ _)
      have hORD : mem3 (A.ORD + k) = mem2 (A.ORD + k) := hfr3 _ (by omega)
      rw [hORD]
      obtain ⟨i, hi, hfi, hP⟩ := (csr_exists_iff (ord := fun k => mem2 (A.ORD + k)) f
        (hord' u (by omega)) (fun i => mem2 (A.ORD + k) = i)).mp ⟨k, hk1, hk2, rfl⟩
      rw [hP]
      have hfi' : mem1 (A.TL + i) = u := hfi
      obtain ⟨e1, -, e3⟩ := hhd k hk
      have e1' : mem3 (A.HD + k) = mem1 (A.HDt + i) := by rw [e1, hP]
      have e2' : mem3 (A.CS + k) = mem1 (A.CSt + i) := by rw [(hhd k hk).2.1, hP]
      have e3' : mem3 (A.CL + k) = mem1 (A.CLt + i) := by rw [e3, hP]
      rw [e1', e2', e3']
      obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hD1 (i / 2) (by show i / 2 < A.nS; omega)
      simp only [startState, eF1, eF2, eF3, eF4] at d1 d2 d3 d4 d5 d6 d7 d8
      rcases Nat.even_or_odd i with ⟨r, hr⟩ | ⟨r, hr⟩
      · have ei : i = 2 * (i / 2) := by omega
        rw [← ei] at d1 d3 d5 d7
        rw [hfi'] at d1
        have hkp : F.keep mem (i / 2) := by
          by_contra hn; simp only [AF.ta, hn, if_false, eF6] at d1; omega
        simp only [AF.ta, AF.tb, AF.cs, AF.cc, hkp, if_true] at d1 d3 d5 d7
        exact ⟨by omega, hkp, Or.inl ⟨d1.symm, d3⟩, d5, d7⟩
      · have ei : i = 2 * (i / 2) + 1 := by omega
        rw [Nat.add_assoc, ← ei] at d2 d4 d6 d8
        rw [hfi'] at d2
        have hkp : F.keep mem (i / 2) := by
          by_contra hn; simp only [AF.tb, hn, if_false, eF6] at d2; omega
        simp only [AF.ta, AF.tb, AF.cs, AF.cc, hkp, if_true] at d2 d4 d6 d8
        exact ⟨by omega, hkp, Or.inr ⟨d2.symm, d4⟩, d6, d8⟩
    · rw [hfr3 a (by omega), hfr2 a (by simp only [csrOut]; omega), hm10 a (by omega)]
  · simp only [arcPC, arcFillC, csrC, arcCopyC, AP.args, List.getD_cons_zero,
      List.getD_cons_succ, startState]
    wram_cost

end MinCostFlow.LowStretch
