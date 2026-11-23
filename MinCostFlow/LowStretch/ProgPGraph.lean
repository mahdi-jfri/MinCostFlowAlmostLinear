module

public import MinCostFlow.LowStretch.ProgSlot
public import MinCostFlow.LowStretch.ProgArcs2
public import MinCostFlow.LowStretch.PSumCSR

/-!
# The petal graph of a cluster

`pgP` builds the graph in which the petals are grown. It writes the pair items (`pfill`) and
the highway slots (`slotF`), groups all items by their tails (`csrB`) and copies them in that
order (`arcCopy`). The slot of node `u` has the largest item number among the items of `u`, so
it is the last arc of `u`. The other arcs of `u` are the two directions of the active pairs at
`u`, with their rounded costs and classes (`pgP_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

section csr

variable (f : ℕ → ℕ)

/-- With `M0` items whose keys are below `s`, followed by one item of key `u` for each `u < s`,
the items of key `u` are those below `M0` and then its own item. -/
theorem grp_slots {M0 s : ℕ} (h2 : ∀ u < s, f (M0 + u) = u) {u : ℕ} (hu : u < s) :
    grp f (M0 + s) u = grp f M0 u ++ [M0 + u] := by
  have key : ∀ k ≤ s, grp f (M0 + k) u = grp f M0 u ++ (if u < k then [M0 + u] else []) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← Nat.add_assoc, grp_succ, ih (by omega), h2 k (by omega)]
      by_cases e : k = u
      · subst e; simp
      · have : (u < k + 1) ↔ (u < k) := by omega
        by_cases h' : u < k
        · simp [h', e, show u < k + 1 by omega]
        · simp [h', e, show ¬ u < k + 1 by omega]
  rw [key s le_rfl, if_pos hu]

/-- **The cells of a key before its last one.** If the items of key `u` end with item
`M0 + u`, then the cells of `u` other than the last hold exactly the items below `M0` of key
`u`. -/
theorem csr_front_iff {M M0 u : ℕ} {ord : ℕ → ℕ}
    (hord : ∀ j < (grp f M u).length, ord (offOf f M u + j) = (grp f M u).getD j 0)
    (hg : grp f M u = grp f M0 u ++ [M0 + u]) (P : ℕ → Prop) :
    (∃ k, offOf f M u ≤ k ∧ k + 1 < offOf f M (u + 1) ∧ P (ord k)) ↔
      ∃ i < M0, f i = u ∧ P i := by
  rw [offOf_succ, hg]
  simp only [List.length_append, List.length_singleton]
  constructor
  · rintro ⟨k, hk1, hk2, hP⟩
    obtain ⟨j, rfl⟩ : ∃ j, k = offOf f M u + j := ⟨k - offOf f M u, by omega⟩
    have hj : j < (grp f M0 u).length := by omega
    rw [hord j (by rw [hg]; simp; omega), hg, List.getD_append _ _ _ _ hj] at hP
    have hmem : (grp f M0 u).getD j 0 ∈ grp f M0 u := by
      rw [List.getD_eq_getElem _ _ hj]; exact List.getElem_mem hj
    unfold grp at hmem
    simp only [List.mem_filter, List.mem_range, decide_eq_true_eq] at hmem
    exact ⟨_, hmem.1, hmem.2, hP⟩
  · rintro ⟨i, hi, hfi, hP⟩
    have hmem : i ∈ grp f M0 u := by
      unfold grp; simp [hi, hfi]
    obtain ⟨j, hj, hji⟩ := List.mem_iff_getElem.mp hmem
    refine ⟨offOf f M u + j, by omega, by omega, ?_⟩
    rw [hord j (by rw [hg]; simp; omega), hg, List.getD_append _ _ _ _ hj,
      List.getD_eq_getElem _ _ hj, hji]
    exact hP

/-- The last cell of key `u` holds item `M0 + u`. -/
theorem csr_last {M M0 u : ℕ} {ord : ℕ → ℕ}
    (hord : ∀ j < (grp f M u).length, ord (offOf f M u + j) = (grp f M u).getD j 0)
    (hg : grp f M u = grp f M0 u ++ [M0 + u]) :
    offOf f M u < offOf f M (u + 1) ∧ ord (offOf f M (u + 1) - 1) = M0 + u := by
  rw [offOf_succ, hg]
  simp only [List.length_append, List.length_singleton]
  refine ⟨by omega, ?_⟩
  have := hord (grp f M0 u).length (by rw [hg]; simp)
  rw [hg] at this
  rw [show offOf f M u + ((grp f M0 u).length + 1) - 1 = offOf f M u + (grp f M0 u).length by
    omega, this]
  simp

end csr

/-- The classes that `pfill` gives are below `Jc + 2`, and their costs are words. -/
theorem rcK_lt {lθ x J : ℕ} (h : 2 * x ≤ 2 ^ (lθ + (J - 1))) (hJ : 1 ≤ J) : rcK lθ x < J + 2 := by
  unfold rcK rcE
  split_ifs with hx
  · omega
  · have : Nat.clog 2 (2 * x) ≤ lθ + (J - 1) := Nat.clog_le_of_le_pow h
    omega

theorem cofK_le {lθ k J : ℕ} (hk : k < J + 2) (hJ : 1 ≤ J) : cofK lθ k ≤ 2 ^ (lθ + J) := by
  unfold cofK
  split_ifs
  · exact Nat.zero_le _
  · exact Nat.pow_le_pow_right (by norm_num) (by omega)

/-- The addresses and numbers that `pgP` uses. -/
structure PGA where
  nA : ℕ
  AS : ℕ
  IN : ℕ
  PW : ℕ
  LAB : ℕ
  LOC : ℕ
  DV : ℕ
  lθ : ℕ
  Jc : ℕ
  TL : ℕ
  HDt : ℕ
  CSt : ℕ
  CLt : ℕ
  NI : ℕ
  s : ℕ
  x0 : ℕ
  PC : ℕ
  CS1 : ℕ
  CL1 : ℕ
  OFF : ℕ
  CNT : ℕ
  ORD : ℕ
  HD : ℕ
  CS : ℕ
  CL : ℕ
  OK : ℕ
  os : ℕ

namespace PGA

variable (A : PGA)

def args : List ℕ :=
  [A.nA, A.AS, A.IN, A.PW, A.LAB, A.LOC, A.DV, A.lθ, A.Jc, A.TL, A.HDt, A.CSt, A.CLt, A.NI,
    A.s, A.x0, A.PC, A.CS1, A.CL1, A.OFF, A.CNT, A.ORD, A.HD, A.CS, A.CL, A.OK, A.os]

theorem eq_of_args {A A' : PGA} (h : A.args = A'.args) : A' = A := by
  cases A; cases A'; simp only [PGA.args, List.cons.injEq] at h
  simp_all

def toPF : PF := ⟨A.nA, A.AS, A.IN, A.PW, A.LAB, A.LOC, A.DV, A.lθ, A.Jc, A.TL, A.HDt, A.CSt,
  A.CLt, A.NI⟩

def toSF : SF := ⟨2 * A.nA, A.s, A.x0, A.PC, A.CS1, A.CL1, A.TL, A.HDt, A.CSt, A.CLt⟩

def toAC : AC := ⟨2 * A.nA + A.s, A.ORD, A.HDt, A.CSt, A.CLt, A.HD, A.CS, A.CL, A.OK, A.s, A.os⟩

/-- The precondition of `pgP`. The parent arcs of the nodes are below `MM`. -/
structure Pre (w : ℕ) (mem : ℕ → ℕ) (m n NL NS MM : ℕ) : Prop where
  fill : A.toPF.Pre mem w m n NL NS
  ea_lt : ∀ j < A.nA, A.toPF.ea mem j < A.s
  eb_lt : ∀ j < A.nA, A.toPF.eb mem j < A.s
  pc : ∀ u < A.s, u ≠ A.x0 → mem (A.PC + u) < MM
  vc : ∀ k < MM, mem (A.CS1 + k) < 2 ^ w ∧ mem (A.CL1 + k) < 2 ^ w
  rPC : A.PC + A.s ≤ A.TL
  rCS : A.CS1 + MM ≤ A.TL
  rCL : A.CL1 + MM ≤ A.TL
  hNI2 : 2 * A.nA + A.s ≤ A.NI
  lO : A.CLt + A.NI ≤ A.OFF
  lC : A.OFF + A.s + 2 ≤ A.CNT
  lD : A.CNT + A.s + 1 ≤ A.ORD
  lH : A.ORD + A.NI ≤ A.HD
  lCS : A.HD + A.NI ≤ A.CS
  lCL : A.CS + A.NI ≤ A.CL
  lOK : A.CL + A.NI ≤ A.OK
  lw : A.OK + A.s + 3 < 2 ^ w
  los : A.os + 1 < 2 ^ w

end PGA

/-- `pgP bP bS bC bY` with `args = A.args`; `pfill`, `slotF`, `csrB` and `arcCopy` sit at `bP`,
`bS`, `bC` and `bY`. -/
def pgP (bP bS bC bY : ℕ) : Stmt :=
  .seq (.call 27 bP [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6, .reg 7, .reg 8,
    .reg 9, .reg 10, .reg 11, .reg 12, .reg 13])
  (.seq (.call 27 bS [.bin .mul (.const 2) (.reg 0), .reg 14, .reg 15, .reg 16, .reg 17, .reg 18,
    .reg 9, .reg 10, .reg 11, .reg 12])
  (.seq (.call 27 bC [.reg 9, .bin .add (.bin .mul (.const 2) (.reg 0)) (.reg 14),
    .bin .add (.reg 14) (.const 1), .reg 19, .reg 20, .reg 21])
  (.seq (.call 27 bY [.bin .add (.bin .mul (.const 2) (.reg 0)) (.reg 14), .reg 21, .reg 10,
    .reg 11, .reg 12, .reg 22, .reg 23, .reg 24, .reg 25, .reg 14, .reg 26])
  (.ret (.const 0)))))

theorem pgP_noRand (bP bS bC bY : ℕ) : (pgP bP bS bC bY).NoRand := by simp [pgP, Stmt.NoRand]

/-- The contract of `pgP`. Node `u < s` has the cells `OFF[u], …, OFF[u + 1] - 1`. The last one
is its slot, with head `s`. The others are the two directions of the active pairs at `u`. -/
def pgPC (w : ℕ) : Contract where
  pre args mem := ∃ A : PGA, ∃ m n NL NS MM, args = A.args ∧ A.Pre w mem m n NL NS MM
  post args mem _ mem' := ∀ A : PGA, args = A.args →
    mem' A.OFF = 0 ∧ (∀ u < A.s + 1, mem' (A.OFF + u) ≤ mem' (A.OFF + 1 + u)) ∧
    mem' (A.OFF + A.s) = 2 * A.nA + A.s ∧ mem' (A.OFF + 1 + A.s) = 2 * A.nA + A.s ∧
    (∀ u < A.s, mem' (A.OFF + u) < mem' (A.OFF + 1 + u) ∧
      mem' (A.HD + (mem' (A.OFF + 1 + u) - 1)) = A.s ∧
      mem' (A.CS + (mem' (A.OFF + 1 + u) - 1)) = A.toSF.sc mem u ∧
      mem' (A.CL + (mem' (A.OFF + 1 + u) - 1)) = A.toSF.sk mem u) ∧
    (∀ u < A.s, ∀ P : ℕ → ℕ → ℕ → Prop,
      (∃ k, mem' (A.OFF + u) ≤ k ∧ k + 1 < mem' (A.OFF + 1 + u) ∧
        P (mem' (A.HD + k)) (mem' (A.CS + k)) (mem' (A.CL + k))) ↔
      ∃ j < A.nA,
        (A.toPF.ea mem j = u ∧ P (A.toPF.eb mem j) (cofK A.lθ (A.toPF.k1 mem j)) (A.toPF.k1 mem j)) ∨
        (A.toPF.eb mem j = u ∧ P (A.toPF.ea mem j) (cofK A.lθ (A.toPF.k2 mem j)) (A.toPF.k2 mem j))) ∧
    (∀ k < 2 * A.nA + A.s, mem' (A.HD + k) < A.s + 1 ∧
      ((∃ j < A.nA, (mem' (A.CS + k) = cofK A.lθ (A.toPF.k1 mem j) ∧
          mem' (A.CL + k) = A.toPF.k1 mem j) ∨
        (mem' (A.CS + k) = cofK A.lθ (A.toPF.k2 mem j) ∧ mem' (A.CL + k) = A.toPF.k2 mem j)) ∨
       ∃ u < A.s, mem' (A.CS + k) = A.toSF.sc mem u ∧ mem' (A.CL + k) = A.toSF.sk mem u)) ∧
    (∀ v < A.s, mem' (A.OK + v) = A.os) ∧ mem' (A.OK + A.s) = A.os + 1 ∧
    (∀ a, ¬ (A.TL ≤ a ∧ a ≤ A.OK + A.s) → mem' a = mem a) ∧
    ∀ u < A.s, ∀ Fs : ℕ → ℕ → ℕ,
      ∑ k ∈ Finset.Ico (mem' (A.OFF + u)) (mem' (A.OFF + 1 + u) - 1),
          Fs (mem' (A.HD + k)) (mem' (A.ORD + k) / 2) =
        ∑ j ∈ (Finset.range A.nA).filter (A.toPF.ea mem · = u), Fs (A.toPF.eb mem j) j +
        ∑ j ∈ (Finset.range A.nA).filter (A.toPF.eb mem · = u), Fs (A.toPF.ea mem j) j
  cost args _ := args.getD 0 0 * (80 * Nat.clog 2 (args.getD 8 0) + 1000) +
    500 * args.getD 14 0 + 500

set_option maxHeartbeats 4000000 in
theorem pgP_spec {w : ℕ} {p : Program} {b bP bR bS bC bY : ℕ}
    (hp : p.HasAt b [pgP bP bS bC bY]) (hP : p.HasAt bP [pfill bR])
    (hR : MeetsContract w p bR (rclsC w)) (hS : p.HasAt bS [slotF]) (hC : p.HasAt bC [csrB])
    (hY : p.HasAt bY [arcCopy]) : MeetsContract w p b (pgPC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨A, m, n, NL, NS, MM, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some (pgP bP bS bC bY) := hp 0 (by simp)
  have sP := pfill_spec (w := w) hP hR
  have sS := slotF_spec (w := w) hS
  have sC := csrB_spec (w := w) hC
  have sY := arcCopy_spec (w := w) hY
  clear hp hP hS hC hY
  have hf := h.fill
  have l1 := hf.l1; have l2 := hf.l2; have l3 := hf.l3; have l4 := hf.l4
  have rAS := hf.rAS; have rIN := hf.rIN; have rPW := hf.rPW; have rLAB := hf.rLAB
  have rLOC := hf.rLOC; have rDV := hf.rDV; have hJ := hf.hJ; have hJ2 := hf.hJ2
  have hJc1 := hf.Jc1
  have rPC := h.rPC; have rCS := h.rCS; have rCL := h.rCL; have hNI2 := h.hNI2
  have lO := h.lO; have lC := h.lC; have lD := h.lD; have lH := h.lH; have lCS := h.lCS
  have lCL := h.lCL; have lOK := h.lOK; have lw := h.lw; have los := h.los
  have hea := h.ea_lt
  have heb := h.eb_lt
  have hw1 : 1 < 2 ^ w := by omega
  set F := A.toPF with hF
  set S := A.toSF with hS
  have eF : F.nA = A.nA ∧ F.TL = A.TL ∧ F.HDt = A.HDt ∧ F.CSt = A.CSt ∧ F.CLt = A.CLt ∧
      F.NI = A.NI ∧ F.lθ = A.lθ ∧ F.Jc = A.Jc := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨eF0, eF1, eF2, eF3, eF4, eF5, eF6, eF7⟩ := eF
  rw [eF1, eF2, eF5] at l1; rw [eF2, eF3, eF5] at l2; rw [eF3, eF4, eF5] at l3
  rw [eF4, eF5] at l4; rw [eF6, eF7] at hJ hJ2; rw [eF7] at hJc1
  have hwA : ∀ a ∈ A.args, a < 2 ^ w := hwords
  simp only [PGA.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hwA
  refine ⟨pgP bP bS bC bY, hproc, ?_⟩
  dsimp only [pgP]
  refine runs_start_le ?_
  have g0 : A.args[0]?.getD 0 = A.nA := rfl
  have g1 : A.args[1]?.getD 0 = A.AS := rfl
  have g2 : A.args[2]?.getD 0 = A.IN := rfl
  have g3 : A.args[3]?.getD 0 = A.PW := rfl
  have g4 : A.args[4]?.getD 0 = A.LAB := rfl
  have g5 : A.args[5]?.getD 0 = A.LOC := rfl
  have g6 : A.args[6]?.getD 0 = A.DV := rfl
  have g7 : A.args[7]?.getD 0 = A.lθ := rfl
  have g8 : A.args[8]?.getD 0 = A.Jc := rfl
  have g9 : A.args[9]?.getD 0 = A.TL := rfl
  have g10 : A.args[10]?.getD 0 = A.HDt := rfl
  have g11 : A.args[11]?.getD 0 = A.CSt := rfl
  have g12 : A.args[12]?.getD 0 = A.CLt := rfl
  have g13 : A.args[13]?.getD 0 = A.NI := rfl
  have g14 : A.args[14]?.getD 0 = A.s := rfl
  have g15 : A.args[15]?.getD 0 = A.x0 := rfl
  have g16 : A.args[16]?.getD 0 = A.PC := rfl
  have g17 : A.args[17]?.getD 0 = A.CS1 := rfl
  have g18 : A.args[18]?.getD 0 = A.CL1 := rfl
  have g19 : A.args[19]?.getD 0 = A.OFF := rfl
  have g20 : A.args[20]?.getD 0 = A.CNT := rfl
  have g21 : A.args[21]?.getD 0 = A.ORD := rfl
  have g22 : A.args[22]?.getD 0 = A.HD := rfl
  have g23 : A.args[23]?.getD 0 = A.CS := rfl
  have g24 : A.args[24]?.getD 0 = A.CL := rfl
  have g25 : A.args[25]?.getD 0 = A.OK := rfl
  have g26 : A.args[26]?.getD 0 = A.os := rfl
  -- `pfill`
  wram_step
  · exact ⟨F, m, n, NL, NS, by simp [PGA.args, PF.args, hF, PGA.toPF], hf⟩
  intro v1 mem1 pos1 hpost1
  obtain ⟨hD1, hfr1⟩ := hpost1 F rfl
  clear hpost1
  have hm10 : ∀ a, (a < A.TL ∨ A.CLt + A.NI ≤ a) → mem1 a = mem a := fun a ha =>
    hfr1 a (by unfold PF.Out; rw [eF0, eF1, eF2, eF3, eF4]; omega)
  have hsc : ∀ u < A.s, S.sc mem1 u = S.sc mem u ∧ S.sk mem1 u = S.sk mem u := by
    intro u hu
    by_cases hx : u = A.x0
    · simp [SF.sc, SF.sk, hS, PGA.toSF, hx]
    · have hpc := h.pc u hu hx
      have e1 : mem1 (A.PC + u) = mem (A.PC + u) := hm10 _ (by omega)
      simp only [SF.sc, SF.sk, hS, PGA.toSF, hx, if_false, e1]
      exact ⟨hm10 _ (by omega), hm10 _ (by omega)⟩
  -- `slotF`
  wram_step
  · refine ⟨S, MM, by simp [SF.args, hS, PGA.toSF], ?_⟩
    exact { pc := fun u hu hx => by
              simp only [hS, PGA.toSF] at hu hx ⊢
              rw [hm10 _ (by omega)]; exact h.pc u hu hx
            rPC := by simp only [hS, PGA.toSF]; omega
            rCS := by simp only [hS, PGA.toSF]; omega
            rCL := by simp only [hS, PGA.toSF]; omega
            l1 := by simp only [hS, PGA.toSF]; omega
            l2 := by simp only [hS, PGA.toSF]; omega
            l3 := by simp only [hS, PGA.toSF]; omega
            l4 := by simp only [hS, PGA.toSF]; omega
            hw := hw1 }
  intro v2 mem2 pos2 hpost2
  obtain ⟨hD2, hfr2⟩ := hpost2 S rfl
  clear hpost2
  have hm21 : ∀ a, (a < A.TL + 2 * A.nA ∨ A.CLt + A.NI ≤ a ∨
      (A.TL + A.NI ≤ a ∧ a < A.HDt + 2 * A.nA) ∨ (A.HDt + A.NI ≤ a ∧ a < A.CSt + 2 * A.nA) ∨
      (A.CSt + A.NI ≤ a ∧ a < A.CLt + 2 * A.nA)) → mem2 a = mem1 a := fun a ha =>
    hfr2 a (by unfold SF.Out; simp only [hS, PGA.toSF]; omega)
  -- the items after the two fills
  have hitem : ∀ i < 2 * A.nA + A.s,
      (i < 2 * A.nA → ∃ j < A.nA,
        (i = 2 * j ∧ mem2 (A.TL + i) = F.ea mem j ∧ mem2 (A.HDt + i) = F.eb mem j ∧
          mem2 (A.CSt + i) = cofK A.lθ (F.k1 mem j) ∧ mem2 (A.CLt + i) = F.k1 mem j) ∨
        (i = 2 * j + 1 ∧ mem2 (A.TL + i) = F.eb mem j ∧ mem2 (A.HDt + i) = F.ea mem j ∧
          mem2 (A.CSt + i) = cofK A.lθ (F.k2 mem j) ∧ mem2 (A.CLt + i) = F.k2 mem j)) ∧
      (2 * A.nA ≤ i → mem2 (A.TL + i) = i - 2 * A.nA ∧ mem2 (A.HDt + i) = A.s ∧
        mem2 (A.CSt + i) = S.sc mem (i - 2 * A.nA) ∧ mem2 (A.CLt + i) = S.sk mem (i - 2 * A.nA)) := by
    intro i hi
    refine ⟨fun hi2 => ?_, fun hi2 => ?_⟩
    · obtain ⟨j, hj⟩ : ∃ j, j = i / 2 := ⟨_, rfl⟩
      obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hD1 j (by rw [eF0]; omega)
      rw [eF1] at d1 d2; rw [eF2] at d3 d4; rw [eF3, eF6] at d5 d6; rw [eF4] at d7 d8
      refine ⟨j, by omega, ?_⟩
      rcases Nat.even_or_odd i with ⟨k, hk⟩ | ⟨k, hk⟩
      · have e : i = 2 * j := by omega
        refine Or.inl ⟨e, ?_, ?_, ?_, ?_⟩ <;> rw [hm21 _ (by omega), e] <;> assumption
      · have e : i = 2 * j + 1 := by omega
        refine Or.inr ⟨e, ?_, ?_, ?_, ?_⟩ <;> rw [hm21 _ (by omega), e, ← Nat.add_assoc] <;>
          assumption
    · obtain ⟨d1, d2, d3, d4⟩ := hD2 (i - 2 * A.nA) (by simp only [hS, PGA.toSF]; omega)
      obtain ⟨c1, c2⟩ := hsc (i - 2 * A.nA) (by omega)
      simp only [hS, PGA.toSF] at d1 d2 d3 d4 c1 c2
      have e : A.TL + 2 * A.nA + (i - 2 * A.nA) = A.TL + i := by omega
      have e2 : A.HDt + 2 * A.nA + (i - 2 * A.nA) = A.HDt + i := by omega
      have e3 : A.CSt + 2 * A.nA + (i - 2 * A.nA) = A.CSt + i := by omega
      have e4 : A.CLt + 2 * A.nA + (i - 2 * A.nA) = A.CLt + i := by omega
      rw [e] at d1; rw [e2] at d2; rw [e3] at d3; rw [e4] at d4
      exact ⟨d1, d2, d3.trans c1, d4.trans c2⟩
  have hk1 : ∀ j < A.nA, F.k1 mem j < A.Jc + 2 := fun j hj =>
    rcK_lt (by have := hf.x1_le j (by rw [eF0]; exact hj); rw [eF6, eF7] at this; exact this) hJc1
  have hk2 : ∀ j < A.nA, F.k2 mem j < A.Jc + 2 := fun j hj =>
    rcK_lt (by have := hf.x2_le j (by rw [eF0]; exact hj); rw [eF6, eF7] at this; exact this) hJc1
  have hscw : ∀ u < A.s, S.sc mem u < 2 ^ w ∧ S.sk mem u < 2 ^ w := by
    intro u hu
    by_cases hx : u = A.x0
    · simp only [SF.sc, SF.sk, hS, PGA.toSF, hx, if_true]; omega
    · simp only [SF.sc, SF.sk, hS, PGA.toSF, hx, if_false]
      exact h.vc _ (h.pc u hu hx)
  -- `csrB`
  set f : ℕ → ℕ := fun i => mem2 (A.TL + i) with hfdef
  have hkey : ∀ i < 2 * A.nA + A.s, f i < A.s + 1 := fun i hi => by
    obtain ⟨h1, h2⟩ := hitem i hi
    simp only [hfdef]
    by_cases hi2 : i < 2 * A.nA
    · obtain ⟨j, hj, c⟩ := h1 hi2
      rcases c with ⟨-, e, -⟩ | ⟨-, e, -⟩ <;> rw [e]
      · have := hea j hj; omega
      · have := heb j hj; omega
    · rw [(h2 (by omega)).1]; omega
  wram_step
  · exact ⟨A.TL, 2 * A.nA + A.s, A.s + 1, A.OFF, A.CNT, A.ORD, by simp [PGA.args], hkey,
      by omega, by omega, by omega, by omega⟩
  intro v3 mem3 pos3 hpost3
  simp only [csrC, PGA.args, List.getD_cons_zero, List.getD_cons_succ] at hpost3
  obtain ⟨hoff, hord, hfr3⟩ := hpost3
  have hord' : ∀ u < A.s + 1, ∀ j < (grp f (2 * A.nA + A.s) u).length,
      (fun k => mem3 (A.ORD + k)) (offOf f (2 * A.nA + A.s) u + j) =
        (grp f (2 * A.nA + A.s) u).getD j 0 := by
    intro u hu j hj
    simp only
    rw [← Nat.add_assoc]; exact hord u hu j hj
  have hordlt : ∀ k < 2 * A.nA + A.s, mem3 (A.ORD + k) < 2 * A.nA + A.s := fun k hk =>
    csr_item (ord := fun k => mem3 (A.ORD + k)) f hkey hord' hk
  have hm32 : ∀ a, a < A.OFF → mem3 a = mem2 a := fun a ha =>
    hfr3 a (by simp only [csrOut]; omega)
  -- the values of the items are words
  have hvw : ∀ i < 2 * A.nA + A.s, mem3 (A.HDt + i) < 2 ^ w ∧ mem3 (A.CSt + i) < 2 ^ w ∧
      mem3 (A.CLt + i) < 2 ^ w := by
    intro i hi
    rw [hm32 _ (by omega), hm32 _ (by omega), hm32 _ (by omega)]
    obtain ⟨h1, h2⟩ := hitem i hi
    by_cases hi2 : i < 2 * A.nA
    · obtain ⟨j, hj, c⟩ := h1 hi2
      have := hk1 j hj; have := hk2 j hj
      have := cofK_le (lθ := A.lθ) (hk1 j hj) hJc1
      have := cofK_le (lθ := A.lθ) (hk2 j hj) hJc1
      have := hea j hj; have := heb j hj
      rcases c with ⟨-, -, e2, e3, e4⟩ | ⟨-, -, e2, e3, e4⟩ <;> rw [e2, e3, e4] <;>
        exact ⟨by omega, by omega, by omega⟩
    · obtain ⟨-, e2, e3, e4⟩ := h2 (by omega)
      rw [e2, e3, e4]
      have := hscw (i - 2 * A.nA) (by omega)
      exact ⟨by omega, this.1, this.2⟩
  -- `arcCopy`
  wram_step
  · exact ⟨A.toAC, by simp [AC.args, PGA.toAC],
      { ord := hordlt, vHD := fun i hi => (hvw i hi).1, vCS := fun i hi => (hvw i hi).2.1,
        vCL := fun i hi => (hvw i hi).2.2, r1 := by simp only [PGA.toAC]; omega,
        r2 := by simp only [PGA.toAC]; omega, r3 := by simp only [PGA.toAC]; omega,
        r4 := by simp only [PGA.toAC]; omega, l1 := by simp only [PGA.toAC]; omega,
        l2 := by simp only [PGA.toAC]; omega, l3 := by simp only [PGA.toAC]; omega,
        l4 := by simp only [PGA.toAC]; omega, los := by simp only [PGA.toAC]; omega }⟩
  intro v4 mem4 pos4 hpost4
  obtain ⟨hD4, hmk1, hmk2, hfr4⟩ := hpost4 A.toAC (by simp [AC.args, PGA.toAC])
  clear hpost4
  wram_run
  · dsimp only at hD4 hfr4 ⊢
    simp only [PGA.toAC, AC.Done1, AC.Out] at hD4 hmk1 hmk2 hfr4
    have hoff4 : ∀ u ≤ A.s + 1, mem4 (A.OFF + u) = offOf f (2 * A.nA + A.s) u := fun u hu => by
      rw [hfr4 _ (by omega)]; exact hoff u hu
    have hhd : ∀ k < 2 * A.nA + A.s, mem4 (A.HD + k) = mem2 (A.HDt + mem3 (A.ORD + k)) ∧
        mem4 (A.CS + k) = mem2 (A.CSt + mem3 (A.ORD + k)) ∧
        mem4 (A.CL + k) = mem2 (A.CLt + mem3 (A.ORD + k)) := by
      intro k hk
      obtain ⟨e1, e2, e3⟩ := hD4 k hk
      have := hordlt k hk
      exact ⟨by rw [e1]; exact hm32 _ (by omega), by rw [e2]; exact hm32 _ (by omega),
        by rw [e3]; exact hm32 _ (by omega)⟩
    have hf2 : ∀ u < A.s, f (2 * A.nA + u) = u := fun u hu => by
      simp only [hfdef]
      have := (hitem (2 * A.nA + u) (by omega)).2 (by omega)
      rw [this.1]; omega
    have hg : ∀ u < A.s, grp f (2 * A.nA + A.s) u = grp f (2 * A.nA) u ++ [2 * A.nA + u] :=
      fun u hu => grp_slots f hf2 hu
    have hall : ∀ i < 2 * A.nA + A.s, f i < A.s + 1 := hkey
    have hOs : offOf f (2 * A.nA + A.s) A.s = 2 * A.nA + A.s := by
      apply offOf_all
      intro i hi
      obtain ⟨h1, h2⟩ := hitem i hi
      simp only [hfdef]
      by_cases hi2 : i < 2 * A.nA
      · obtain ⟨j, hj, c⟩ := h1 hi2
        rcases c with ⟨-, e, -⟩ | ⟨-, e, -⟩ <;> rw [e]
        · exact hea j hj
        · exact heb j hj
      · rw [(h2 (by omega)).1]; omega
    intro A' hA'
    rw [PGA.eq_of_args hA']
    have hpair : ∀ j < A.nA, mem2 (A.TL + 2 * j) = F.ea mem j ∧
        mem2 (A.HDt + 2 * j) = F.eb mem j ∧ mem2 (A.CSt + 2 * j) = cofK A.lθ (F.k1 mem j) ∧
        mem2 (A.CLt + 2 * j) = F.k1 mem j ∧ mem2 (A.TL + (2 * j + 1)) = F.eb mem j ∧
        mem2 (A.HDt + (2 * j + 1)) = F.ea mem j ∧
        mem2 (A.CSt + (2 * j + 1)) = cofK A.lθ (F.k2 mem j) ∧
        mem2 (A.CLt + (2 * j + 1)) = F.k2 mem j := by
      intro j hj
      obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hD1 j (by rw [eF0]; exact hj)
      rw [eF1] at d1 d2; rw [eF2] at d3 d4; rw [eF3, eF6] at d5 d6; rw [eF4] at d7 d8
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
        (try rw [← Nat.add_assoc]) <;> rw [hm21 _ (by omega)] <;> assumption
    have hMle : ∀ u, offOf f (2 * A.nA + A.s) u ≤ 2 * A.nA + A.s := fun u => offOf_le f _ _
    refine ⟨?_, fun u hu => ?_, ?_, ?_, fun u hu => ?_, fun u hu P => ?_, fun k hk => ?_, hmk1,
      hmk2, fun a ha => ?_, fun u hu Fs => ?_⟩
    · have := hoff4 0 (by omega)
      rw [Nat.add_zero, offOf_zero] at this; exact this
    · rw [show A.OFF + 1 + u = A.OFF + (u + 1) by omega, hoff4 u (by omega),
        hoff4 (u + 1) (by omega)]
      exact offOf_mono f (by omega)
    · rw [hoff4 _ (by omega), hOs]
    · rw [show A.OFF + 1 + A.s = A.OFF + (A.s + 1) by omega, hoff4 _ le_rfl]
      exact offOf_all f hall
    · rw [show A.OFF + 1 + u = A.OFF + (u + 1) by omega, hoff4 u (by omega),
        hoff4 (u + 1) (by omega)]
      obtain ⟨hl1, hl2⟩ := csr_last f (ord := fun k => mem3 (A.ORD + k)) (hord' u (by omega)) (hg u hu)
      have e : mem3 (A.ORD + (offOf f (2 * A.nA + A.s) (u + 1) - 1)) = 2 * A.nA + u := hl2
      have hk : offOf f (2 * A.nA + A.s) (u + 1) - 1 < 2 * A.nA + A.s := by
        have := hMle (u + 1); omega
      obtain ⟨c1, c2, c3⟩ := hhd _ hk
      obtain ⟨-, d2, d3, d4⟩ := (hitem (2 * A.nA + u) (by omega)).2 (by omega)
      rw [Nat.add_sub_cancel_left] at d3 d4
      rw [c1, c2, c3, e, d2, d3, d4]
      exact ⟨hl1, rfl, rfl, rfl⟩
    · rw [show A.OFF + 1 + u = A.OFF + (u + 1) by omega, hoff4 u (by omega),
        hoff4 (u + 1) (by omega)]
      have key := csr_front_iff f (ord := fun k => mem3 (A.ORD + k)) (hord' u (by omega)) (hg u hu)
        (fun i => P (mem2 (A.HDt + i)) (mem2 (A.CSt + i)) (mem2 (A.CLt + i)))
      have hlt : ∀ k, k + 1 < offOf f (2 * A.nA + A.s) (u + 1) → k < 2 * A.nA + A.s :=
        fun k hk => by have := hMle (u + 1); omega
      constructor
      · rintro ⟨k, h1, h2, hP⟩
        obtain ⟨c1, c2, c3⟩ := hhd k (hlt k h2)
        rw [c1, c2, c3] at hP
        obtain ⟨i, hi, hfi, hP'⟩ := key.mp ⟨k, h1, h2, hP⟩
        simp only [hfdef] at hfi
        obtain ⟨j, hj, c⟩ := (hitem i (by omega)).1 hi
        refine ⟨j, hj, ?_⟩
        rcases c with ⟨-, e1, e2, e3, e4⟩ | ⟨-, e1, e2, e3, e4⟩
        · rw [e2, e3, e4] at hP'
          exact Or.inl ⟨e1.symm.trans hfi, hP'⟩
        · rw [e2, e3, e4] at hP'
          exact Or.inr ⟨e1.symm.trans hfi, hP'⟩
      · rintro ⟨j, hj, c⟩
        obtain ⟨d1, d2, d3, d4, d5, d6, d7, d8⟩ := hpair j hj
        have hP : ∃ i < 2 * A.nA, f i = u ∧
            P (mem2 (A.HDt + i)) (mem2 (A.CSt + i)) (mem2 (A.CLt + i)) := by
          rcases c with ⟨a1, a2⟩ | ⟨a1, a2⟩
          · exact ⟨2 * j, by omega, by simp only [hfdef]; rw [d1, a1], by rw [d2, d3, d4]; exact a2⟩
          · exact ⟨2 * j + 1, by omega, by simp only [hfdef]; rw [d5, a1],
              by rw [d6, d7, d8]; exact a2⟩
        obtain ⟨k, h1, h2, hP'⟩ := key.mpr hP
        obtain ⟨c1, c2, c3⟩ := hhd k (hlt k h2)
        exact ⟨k, h1, h2, by rw [c1, c2, c3]; exact hP'⟩
    · obtain ⟨c1, c2, c3⟩ := hhd k hk
      have hi := hordlt k hk
      rw [c1, c2, c3]
      obtain ⟨h1, h2⟩ := hitem _ hi
      by_cases hi2 : mem3 (A.ORD + k) < 2 * A.nA
      · obtain ⟨j, hj, c⟩ := h1 hi2
        have := hea j hj; have := heb j hj
        rcases c with ⟨-, -, e2, e3, e4⟩ | ⟨-, -, e2, e3, e4⟩ <;> rw [e2, e3, e4]
        · exact ⟨by omega, Or.inl ⟨j, hj, Or.inl ⟨rfl, rfl⟩⟩⟩
        · exact ⟨by omega, Or.inl ⟨j, hj, Or.inr ⟨rfl, rfl⟩⟩⟩
      · obtain ⟨-, e2, e3, e4⟩ := h2 (by omega)
        rw [e2, e3, e4]
        exact ⟨by omega, Or.inr ⟨_, by omega, rfl, rfl⟩⟩
    · rw [hfr4 a (by omega), hfr3 a (by simp only [csrOut]; omega), hm21 a (by omega),
        hm10 a (by omega)]
    · rw [show A.OFF + 1 + u = A.OFF + (u + 1) by omega, hoff4 u (by omega),
        hoff4 (u + 1) (by omega)]
      have e : ∀ k ∈ Finset.Ico (offOf f (2 * A.nA + A.s) u) (offOf f (2 * A.nA + A.s) (u + 1) - 1),
          Fs (mem4 (A.HD + k)) (mem4 (A.ORD + k) / 2) =
            Fs (mem2 (A.HDt + mem3 (A.ORD + k))) (mem3 (A.ORD + k) / 2) := by
        intro k hk
        have hk' : k < 2 * A.nA + A.s := by
          have := hMle (u + 1); rw [Finset.mem_Ico] at hk; omega
        rw [(hhd k hk').1, hfr4 (A.ORD + k) (by omega)]
      rw [Finset.sum_congr rfl e]
      refine csr_sum (f := f) (ord := fun k => mem3 (A.ORD + k)) (hdA := fun o => mem2 (A.HDt + o))
        (hord' u (by omega)) (hg u hu) (fun o ho => ?_) (fun o ho => ?_) Fs
      · obtain ⟨d1, -, -, -, d5, -, -, -⟩ := hpair (o / 2) (by omega)
        simp only [hfdef, itl]
        split_ifs with h2
        · rw [show A.TL + o = A.TL + 2 * (o / 2) by omega]; exact d1
        · rw [show A.TL + o = A.TL + (2 * (o / 2) + 1) by omega]; exact d5
      · obtain ⟨-, d2, -, -, -, d6, -, -⟩ := hpair (o / 2) (by omega)
        simp only [ihd]
        split_ifs with h2
        · rw [show A.HDt + o = A.HDt + 2 * (o / 2) by omega]; exact d2
        · rw [show A.HDt + o = A.HDt + (2 * (o / 2) + 1) by omega]; exact d6
  · simp only [pgPC, pfillC, slotFC, csrC, arcCopyC, PGA.args, List.getD_cons_zero,
      List.getD_cons_succ, startState]
    have hc : A.nA * (80 * Nat.clog 2 A.Jc + 1000) =
        A.nA * (80 * Nat.clog 2 A.Jc + 500) + 500 * A.nA := by ring
    wram_cost

end MinCostFlow.LowStretch
