module

public import MinCostFlow.LowStretch.ProgPGraph

/-!
# The sums of region growing

When the petal search settles a node `x` with key `k`, the sums of region growing change along
the pair arcs of `x` (`psum`). Arc `k'` goes to `y = HD[k']`, and its pair is entry `ORD[k'] / 2`
of the active list `AS`, with weight `2^EXP[p]` and scaled weight `wt = 2^(Es - EXP[p])`.
* If `y` is allowed and settled, the pair is now inside the petal: the count `I` grows by `1`,
  and `wt` and `wt · tent(y)` go to the minus parts of `C` and `V'`.
* If `y` is allowed and not settled, the pair now leaves the petal: `wt` and `wt · k` go to the
  plus parts of `C` and `V'`.
The five cells `SUM, …, SUM + 4` hold `I`, `C+`, `C-`, `V'+` and `V'-` (`psum_spec`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- The addresses and numbers that `psum` uses. -/
structure PS where
  lo : ℕ
  hi : ℕ
  k : ℕ
  HD : ℕ
  ORD : ℕ
  AS : ℕ
  EXP : ℕ
  Es : ℕ
  TS : ℕ
  NN : ℕ
  rs : ℕ
  OK : ℕ
  os : ℕ
  SUM : ℕ

namespace PS

variable (F : PS) (mem : ℕ → ℕ)

def args : List ℕ :=
  [F.lo, F.hi, F.k, F.HD, F.ORD, F.AS, F.EXP, F.Es, F.TS, F.NN, F.rs, F.OK, F.os, F.SUM]

theorem eq_of_args {F F' : PS} (h : F.args = F'.args) : F' = F := by
  cases F; cases F'; simp only [PS.args, List.cons.injEq] at h
  simp_all

/-- The head of arc `j`. -/
def y (j : ℕ) : ℕ := mem (F.HD + j)
/-- The pair of arc `j`. -/
def pa (j : ℕ) : ℕ := mem (F.AS + 2 * (mem (F.ORD + j) >>> 1))
/-- The scaled weight of arc `j`. -/
def wt (j : ℕ) : ℕ := 1 <<< (F.Es - mem (F.EXP + F.pa mem j))
/-- The head of arc `j` is allowed. -/
def okc (j : ℕ) : Prop := mem (F.OK + F.y mem j) = F.os
/-- The head of arc `j` is settled. -/
def stc (j : ℕ) : Prop := mem (F.TS + 2 * F.NN + F.y mem j) = F.rs
/-- The tentative cost of the head of arc `j`. -/
def ty (j : ℕ) : ℕ := mem (F.TS + F.NN + F.y mem j)

open Classical in
/-- What arc `j` adds to each of the five cells. -/
noncomputable def gv (j : ℕ) : Fin 5 → ℕ
  | 0 => if F.okc mem j ∧ F.stc mem j then 1 else 0
  | 1 => if F.okc mem j ∧ ¬ F.stc mem j then F.wt mem j else 0
  | 2 => if F.okc mem j ∧ F.stc mem j then F.wt mem j else 0
  | 3 => if F.okc mem j ∧ ¬ F.stc mem j then F.wt mem j * F.k else 0
  | 4 => if F.okc mem j ∧ F.stc mem j then F.wt mem j * F.ty mem j else 0

/-- The sum of what the arcs `lo, …, i - 1` add to cell `t`. -/
noncomputable def sm (t : Fin 5) (i : ℕ) : ℕ := ∑ j ∈ Finset.Ico F.lo i, F.gv mem j t

open Classical in
/-- The most that arc `j` can add to each cell. -/
noncomputable def gu (j : ℕ) : Fin 5 → ℕ
  | 0 => 1
  | 1 => F.wt mem j
  | 2 => F.wt mem j
  | 3 => F.wt mem j * F.k
  | 4 => if F.okc mem j ∧ F.stc mem j then F.wt mem j * F.ty mem j else 0

/-- The most that the arcs `lo, …, i - 1` can add to cell `t`. -/
noncomputable def ub (t : Fin 5) (i : ℕ) : ℕ := ∑ j ∈ Finset.Ico F.lo i, F.gu mem j t

/-- The precondition of `psum`: the arrays it reads lie below `SUM`, and all values are words. -/
structure Pre (w : ℕ) : Prop where
  hle : F.lo ≤ F.hi
  rHD : F.HD + F.hi ≤ F.SUM
  rORD : F.ORD + F.hi ≤ F.SUM
  rAS : ∀ j, F.lo ≤ j → j < F.hi → F.AS + 2 * (mem (F.ORD + j) >>> 1) < F.SUM
  rEXP : ∀ j, F.lo ≤ j → j < F.hi → F.EXP + F.pa mem j < F.SUM
  rY : ∀ j, F.lo ≤ j → j < F.hi → F.OK + F.y mem j < F.SUM ∧ F.TS + 2 * F.NN + F.y mem j < F.SUM
  wwt : ∀ j, F.lo ≤ j → j < F.hi → F.wt mem j < 2 ^ w
  wk : ∀ j, F.lo ≤ j → j < F.hi → F.wt mem j * F.k < 2 ^ w
  wty : ∀ j, F.lo ≤ j → j < F.hi → F.okc mem j → F.stc mem j → F.wt mem j * F.ty mem j < 2 ^ w
  wsum : ∀ t : Fin 5, mem (F.SUM + t) + F.ub mem t F.hi < 2 ^ w
  wORD : ∀ j, F.lo ≤ j → j < F.hi → mem (F.ORD + j) < 2 ^ w
  wE : ∀ j, F.lo ≤ j → j < F.hi → mem (F.EXP + F.pa mem j) < 2 ^ w
  lw : F.SUM + 5 < 2 ^ w
  lw2 : F.TS + 2 * F.NN < 2 ^ w

end PS

theorem PS.sm_succ (F : PS) (mem : ℕ → ℕ) (t : Fin 5) {i : ℕ} (hi : F.lo ≤ i) :
    F.sm mem t (i + 1) = F.sm mem t i + F.gv mem i t := by
  unfold PS.sm
  rw [Finset.sum_Ico_succ_top hi]

theorem PS.sm_le (F : PS) (mem : ℕ → ℕ) (t : Fin 5) {i j : ℕ} (hij : i ≤ j) :
    F.sm mem t i ≤ F.sm mem t j := by
  unfold PS.sm
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hij)

theorem PS.gv_le (F : PS) (mem : ℕ → ℕ) (j : ℕ) (t : Fin 5) : F.gv mem j t ≤ F.gu mem j t := by
  fin_cases t <;> simp only [PS.gv, PS.gu] <;> split_ifs <;> simp

theorem PS.sm_le_ub (F : PS) (mem : ℕ → ℕ) (t : Fin 5) (i : ℕ) : F.sm mem t i ≤ F.ub mem t i :=
  Finset.sum_le_sum fun j _ => F.gv_le mem j t

theorem PS.ub_succ (F : PS) (mem : ℕ → ℕ) (t : Fin 5) {i : ℕ} (hi : F.lo ≤ i) :
    F.ub mem t (i + 1) = F.ub mem t i + F.gu mem i t := by
  unfold PS.ub
  rw [Finset.sum_Ico_succ_top hi]

theorem PS.ub_le (F : PS) (mem : ℕ → ℕ) (t : Fin 5) {i j : ℕ} (hij : i ≤ j) :
    F.ub mem t i ≤ F.ub mem t j := by
  unfold PS.ub
  exact Finset.sum_le_sum_of_subset (Finset.Ico_subset_Ico le_rfl hij)

/-- The body of `psum`, for arc `j` in register `14`. -/
def psumB : Stmt :=
  .seq (.assign 15 (.load (.bin .add (.reg 3) (.reg 14))))
  (.seq (.assign 16 (.load (.bin .add (.reg 4) (.reg 14))))
  (.seq (.assign 17 (.load (.bin .add (.reg 5)
    (.bin .mul (.const 2) (.bin .shiftRight (.reg 16) (.const 1))))))
  (.seq (.assign 18 (.bin .shiftLeft (.const 1) (.bin .sub (.reg 7)
    (.load (.bin .add (.reg 6) (.reg 17))))))
  (.cond (.bin .eq (.load (.bin .add (.reg 11) (.reg 15))) (.reg 12))
    (.cond (.bin .eq (.load (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9)))
        (.reg 15))) (.reg 10))
      (.seq (.assign 19 (.load (.bin .add (.bin .add (.reg 8) (.reg 9)) (.reg 15))))
      (.seq (.assign 20 (.load (.reg 13)))
      (.seq (.assign 21 (.load (.bin .add (.reg 13) (.const 2))))
      (.seq (.assign 22 (.load (.bin .add (.reg 13) (.const 4))))
      (.seq (.store (.reg 13) (.bin .add (.reg 20) (.const 1)))
      (.seq (.store (.bin .add (.reg 13) (.const 2)) (.bin .add (.reg 21) (.reg 18)))
        (.store (.bin .add (.reg 13) (.const 4))
          (.bin .add (.reg 22) (.bin .mul (.reg 18) (.reg 19))))))))))
      (.seq (.assign 20 (.load (.bin .add (.reg 13) (.const 1))))
      (.seq (.assign 21 (.load (.bin .add (.reg 13) (.const 3))))
      (.seq (.store (.bin .add (.reg 13) (.const 1)) (.bin .add (.reg 20) (.reg 18)))
        (.store (.bin .add (.reg 13) (.const 3))
          (.bin .add (.reg 21) (.bin .mul (.reg 18) (.reg 2))))))))
    .nop))))

/-- `psum` with `args = F.args`. -/
def psum : Stmt := .seq (forRange 14 (.reg 0) (.reg 1) psumB) (.ret (.const 0))

theorem psum_noRand : psum.NoRand := by simp [psum, psumB, forRange, forUp, Stmt.NoRand]

/-- The contract of `psum`. -/
def psumC (w : ℕ) : Contract where
  pre args mem := ∃ F : PS, args = F.args ∧ F.Pre mem w
  post args mem _ mem' := ∀ F : PS, args = F.args →
    (∀ t : Fin 5, mem' (F.SUM + t) = mem (F.SUM + t) + F.sm mem t F.hi) ∧
    ∀ a, (a < F.SUM ∨ F.SUM + 5 ≤ a) → mem' a = mem a
  cost args _ := 200 * (args.getD 1 0 - args.getD 0 0) + 30

set_option maxHeartbeats 4000000 in
theorem psum_spec {w : ℕ} {p : Program} {b : ℕ} (hp : p.HasAt b [psum]) :
    MeetsContract w p b (psumC w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨F, rfl, h⟩ := hpre
  have hproc : p.procs[b]? = some psum := hp 0 (by simp)
  clear hp
  have hle := h.hle; have rHD := h.rHD; have rORD := h.rORD; have lw := h.lw
  have hw1 : 1 < 2 ^ w := by omega
  have hwA : ∀ a ∈ F.args, a < 2 ^ w := hwords
  simp only [PS.args, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq] at hwA
  obtain ⟨wlo, whi, wk, wHD, wORD, wAS, wEXP, wEs, wTS, wNN, wrs, wOK, wos, wSUM⟩ := hwA
  let R : State → Prop := fun st => st.regs 0 = F.lo ∧ st.regs 1 = F.hi ∧ st.regs 2 = F.k ∧
    st.regs 3 = F.HD ∧ st.regs 4 = F.ORD ∧ st.regs 5 = F.AS ∧ st.regs 6 = F.EXP ∧
    st.regs 7 = F.Es ∧ st.regs 8 = F.TS ∧ st.regs 9 = F.NN ∧ st.regs 10 = F.rs ∧
    st.regs 11 = F.OK ∧ st.regs 12 = F.os ∧ st.regs 13 = F.SUM
  have hRu : ∀ st r v, R st → 14 ≤ r → R { st with regs := Function.update st.regs r v } := by
    intro st r v ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ hr
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
      simp only [Function.update_apply] <;> (rw [if_neg (by omega)]; assumption)
  let I : ℕ → State → Prop := fun i st => R st ∧ st.regs 14 = i ∧
    (∀ a, (a < F.SUM ∨ F.SUM + 5 ≤ a) → st.mem a = mem a) ∧
    ∀ t : Fin 5, st.mem (F.SUM + t) = mem (F.SUM + t) + F.sm mem t i
  have hloop := Triple.forRange_const (p := p) (r := 14) (lo := .reg 0) (hi := .reg 1)
    (body := psumB) (P := fun st => R st ∧ st.mem = mem) (Inv := I) 150 F.lo F.hi
    hle hw1 (fun _ => whi)
    (fun st ⟨hr, hm⟩ => ⟨by have := hr.1; eval_expr, hRu st 14 F.lo hr (by omega), by simp,
      fun a _ => by simp [hm], fun t => by simp [hm, PS.sm]⟩)
    (fun _ st _ _ hI => hI.2.1)
    (fun _ st _ _ hI => by have := hI.1.2.1; eval_expr)
    (fun i hi1 hi st ω hI => by
      obtain ⟨hr, h14, hfr, hsum⟩ := hI
      have hr' := hr
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13⟩ := hr
      have hRn : ∀ st' : State, (∀ r < 14, st'.regs r = st.regs r) → R st' := fun st' hs =>
        ⟨(hs 0 (by omega)).trans a0, (hs 1 (by omega)).trans a1, (hs 2 (by omega)).trans a2,
          (hs 3 (by omega)).trans a3, (hs 4 (by omega)).trans a4, (hs 5 (by omega)).trans a5,
          (hs 6 (by omega)).trans a6, (hs 7 (by omega)).trans a7, (hs 8 (by omega)).trans a8,
          (hs 9 (by omega)).trans a9, (hs 10 (by omega)).trans a10, (hs 11 (by omega)).trans a11,
          (hs 12 (by omega)).trans a12, (hs 13 (by omega)).trans a13⟩
      have rAS := h.rAS i hi1 hi
      have rEXP := h.rEXP i hi1 hi
      obtain ⟨rY1, rY2⟩ := h.rY i hi1 hi
      have eY : st.mem (F.HD + i) = F.y mem i := hfr _ (Or.inl (by omega))
      have eO : st.mem (F.ORD + i) = mem (F.ORD + i) := hfr _ (Or.inl (by omega))
      have eA : st.mem (F.AS + 2 * (mem (F.ORD + i) >>> 1)) = F.pa mem i :=
        hfr _ (Or.inl rAS)
      have eE : st.mem (F.EXP + F.pa mem i) = mem (F.EXP + F.pa mem i) := hfr _ (Or.inl rEXP)
      have eOK : st.mem (F.OK + F.y mem i) = mem (F.OK + F.y mem i) := hfr _ (Or.inl rY1)
      have eST : st.mem (F.TS + 2 * F.NN + F.y mem i) = mem (F.TS + 2 * F.NN + F.y mem i) :=
        hfr _ (Or.inl rY2)
      have eTY : st.mem (F.TS + F.NN + F.y mem i) = F.ty mem i := hfr _ (Or.inl (by omega))
      have hwt := h.wwt i hi1 hi
      have hwk := h.wk i hi1 hi
      have hwty := h.wty i hi1 hi
      have hs := fun t => h.wsum t
      have hsi : ∀ t : Fin 5, mem (F.SUM + t) + F.sm mem t i + F.gu mem i t < 2 ^ w := fun t => by
        have h1 := F.sm_le_ub mem t i
        have h2 := F.ub_succ mem t hi1
        have h3 := F.ub_le mem t (show i + 1 ≤ F.hi by omega)
        have h4 := hs t
        omega
      have hsucc := fun t => F.sm_succ mem t hi1
      have hwor := h.wORD i hi1 hi
      have hwe := h.wE i hi1 hi
      have lw2 := h.lw2
      have qORD : st.mem (st.regs 4 + st.regs 14) = mem (F.ORD + i) := by rw [a4, h14, eO]
      have qY : st.mem (st.regs 3 + st.regs 14) = F.y mem i := by rw [a3, h14, eY]
      have qPA : st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1)) = F.pa mem i := by rw [qORD, a5, eA]
      have qE : st.mem (st.regs 6 + st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1))) = mem (F.EXP + F.pa mem i) := by rw [qPA, a6, eE]
      have qWT : 1 <<< (st.regs 7 - st.mem (st.regs 6 + st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1)))) = F.wt mem i := by rw [qE, a7]; rfl
      have qTY : st.mem (st.regs 8 + st.regs 9 + st.mem (st.regs 3 + st.regs 14)) = F.ty mem i := by rw [qY, a8, a9, eTY]
      have hsh : mem (F.ORD + i) >>> 1 ≤ mem (F.ORD + i) := by
        rw [Nat.shiftRight_eq_div_pow]; exact Nat.div_le_self _ _
      have b1 : st.mem (st.regs 4 + st.regs 14) < 2 ^ w := by rw [qORD]; exact hwor
      have b2 : 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1) < 2 ^ w := by rw [qORD]; omega
      have b3 : st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1) < 2 ^ w := by rw [qORD, a5]; omega
      have b4 : st.regs 6 + st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1)) < 2 ^ w := by rw [qPA, a6]; omega
      have b5 : 1 <<< (st.regs 7 - st.mem (st.regs 6 + st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1)))) < 2 ^ w := by rw [qWT]; exact hwt
      have b6 : st.regs 11 + st.mem (st.regs 3 + st.regs 14) < 2 ^ w := by rw [qY, a11]; omega
      have b7 : st.regs 8 + 2 * st.regs 9 + st.mem (st.regs 3 + st.regs 14) < 2 ^ w := by rw [qY, a8, a9]; omega
      have b8 : st.regs 8 + st.regs 9 + st.mem (st.regs 3 + st.regs 14) < 2 ^ w := by rw [qY, a8, a9]; omega
      have b11 : 1 <<< (st.regs 7 - st.mem (st.regs 6 + st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1)))) * st.regs 2 < 2 ^ w := by rw [qWT, a2]; exact hwk
      have eS : ∀ t : Fin 5, st.mem (st.regs 13 + t) = mem (F.SUM + t) + F.sm mem t i := by
        intro t; rw [a13]; exact hsum t
      have eS0 : st.mem (st.regs 13) = mem (F.SUM + 0) + F.sm mem 0 i := by
        have := eS 0; simpa using this
      have eS1 := eS 1
      have eS2 := eS 2
      have eS3 := eS 3
      have eS4 := eS 4
      simp only [Fin.val_one, Fin.val_two] at eS1 eS2
      have e3 : ((3 : Fin 5) : ℕ) = 3 := rfl
      have e4 : ((4 : Fin 5) : ℕ) = 4 := rfl
      rw [e3] at eS3; rw [e4] at eS4
      have g0 := hsucc 0; have g1 := hsucc 1; have g2 := hsucc 2; have g3 := hsucc 3
      have g4 := hsucc 4
      have s0 := hsi 0; have s1 := hsi 1; have s2 := hsi 2; have s3 := hsi 3; have s4 := hsi 4
      simp only [Fin.val_one, Fin.val_two, e3, e4, Fin.val_zero] at s0 s1 s2 s3 s4
      simp only [PS.gv] at g0 g1 g2 g3 g4
      have qTYh : st.mem (st.regs 8 + st.regs 9 + st.mem (F.HD + i)) = F.ty mem i := by rw [eY, a8, a9, eTY]
      have qOKh : (st.mem (st.regs 11 + st.mem (F.HD + i)) = st.regs 12) ↔ F.okc mem i := by rw [eY, a11, a12, eOK]; rfl
      have qSTh : (st.mem (st.regs 8 + 2 * st.regs 9 + st.mem (F.HD + i)) = st.regs 10) ↔ F.stc mem i := by rw [eY, a8, a9, a10, eST]; rfl
      have B0 : st.mem (st.regs 13) + 1 < 2 ^ w := by
        rw [eS0]; simp only [PS.gu, Fin.val_zero, Nat.add_zero] at s0 ⊢; omega
      have B2 : st.mem (st.regs 13 + 2) + 1 <<< (st.regs 7 - st.mem (st.regs 6 + st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1)))) < 2 ^ w := by
        rw [eS2, qWT]; simp only [PS.gu] at s2; omega
      have B4 : ¬ (st.mem (st.regs 11 + st.mem (F.HD + i)) = st.regs 12) ∨
          ¬ (st.mem (st.regs 8 + 2 * st.regs 9 + st.mem (F.HD + i)) = st.regs 10) ∨
          st.mem (st.regs 13 + 4) + 1 <<< (st.regs 7 - st.mem (st.regs 6 + st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1)))) * st.mem (st.regs 8 + st.regs 9 + st.mem (F.HD + i)) < 2 ^ w := by
        by_cases k1 : F.okc mem i
        · by_cases k2 : F.stc mem i
          · right; right
            rw [eS4, qWT, qTYh]; simp only [PS.gu, k1, k2, and_self, if_true] at s4; omega
          · right; left; exact fun hh => k2 (qSTh.mp hh)
        · left; exact fun hh => k1 (qOKh.mp hh)
      have B10 : ¬ (st.mem (st.regs 11 + st.mem (F.HD + i)) = st.regs 12) ∨
          ¬ (st.mem (st.regs 8 + 2 * st.regs 9 + st.mem (F.HD + i)) = st.regs 10) ∨
          1 <<< (st.regs 7 - st.mem (st.regs 6 + st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1)))) * st.mem (st.regs 8 + st.regs 9 + st.mem (F.HD + i)) < 2 ^ w := by
        by_cases k1 : F.okc mem i
        · by_cases k2 : F.stc mem i
          · right; right; rw [qWT, qTYh]; exact hwty k1 k2
          · right; left; exact fun hh => k2 (qSTh.mp hh)
        · left; exact fun hh => k1 (qOKh.mp hh)
      have B1 : st.mem (st.regs 13 + 1) + 1 <<< (st.regs 7 - st.mem (st.regs 6 + st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1)))) < 2 ^ w := by
        rw [eS1, qWT]; simp only [PS.gu] at s1; omega
      have B3 : st.mem (st.regs 13 + 3) + 1 <<< (st.regs 7 - st.mem (st.regs 6 + st.mem (st.regs 5 + 2 * (st.mem (st.regs 4 + st.regs 14) >>> 1)))) * st.regs 2 < 2 ^ w := by
        rw [eS3, qWT, a2]; simp only [PS.gu] at s3; omega
      refine runs_start_le ?_
      dsimp only [psumB]
      wram_run
      all_goals (try wram_cost)
      · have k1 := qOKh.mp ‹_›; have k2 := qSTh.mp ‹_›
        refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
          by simp, fun a ha => ?_, fun t => ?_⟩, by simp [h14]⟩
        · try simp only [a13]
          (try simp (disch := omega) only [Function.update_of_ne])
          exact hfr a ha
        · fin_cases t <;>
            simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.val_zero,
              Fin.val_one, Fin.val_two, e3, e4, Nat.add_zero] <;>
            (try simp only [g0, g1, g2, g3, g4, k1, k2, and_self, and_true, and_false, true_and,
              false_and, not_true_eq_false, not_false_eq_true, ite_true, ite_false, Nat.add_zero]) <;>
            (try simp only [a13]) <;>
            (try simp (disch := omega) only [Function.update_of_ne, Function.update_self]) <;>
            (try simp only [← a13, eS0, eS1, eS2, eS3, eS4, qWT, qTYh, a2, Nat.add_zero]) <;>
            (try rfl) <;> omega
      · have k1 := qOKh.mp ‹_›; have k2 : ¬ F.stc mem i := fun hh => hcond (qSTh.mpr hh)
        refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
          by simp, fun a ha => ?_, fun t => ?_⟩, by simp [h14]⟩
        · try simp only [a13]
          (try simp (disch := omega) only [Function.update_of_ne])
          exact hfr a ha
        · fin_cases t <;>
            simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.val_zero,
              Fin.val_one, Fin.val_two, e3, e4, Nat.add_zero] <;>
            (try simp only [g0, g1, g2, g3, g4, k1, k2, and_self, and_true, and_false, true_and,
              false_and, not_true_eq_false, not_false_eq_true, ite_true, ite_false, Nat.add_zero]) <;>
            (try simp only [a13]) <;>
            (try simp (disch := omega) only [Function.update_of_ne, Function.update_self]) <;>
            (try simp only [← a13, eS0, eS1, eS2, eS3, eS4, qWT, qTYh, a2, Nat.add_zero]) <;>
            (try rfl) <;> omega
      · have k1 : ¬ F.okc mem i := fun hh => hcond (qOKh.mpr hh); have k2 : True := trivial
        refine ⟨⟨hRn _ (fun r hr => by simp (disch := omega) only [Function.update_of_ne]),
          by simp, fun a ha => ?_, fun t => ?_⟩, by simp [h14]⟩
        · try simp only [a13]
          (try simp (disch := omega) only [Function.update_of_ne])
          exact hfr a ha
        · fin_cases t <;>
            simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Fin.isValue, Fin.val_zero,
              Fin.val_one, Fin.val_two, e3, e4, Nat.add_zero] <;>
            (try simp only [g0, g1, g2, g3, g4, k1, k2, and_self, and_true, and_false, true_and,
              false_and, not_true_eq_false, not_false_eq_true, ite_true, ite_false, Nat.add_zero]) <;>
            (try simp only [a13]) <;>
            (try simp (disch := omega) only [Function.update_of_ne, Function.update_self]) <;>
            (try simp only [← a13, eS0, eS1, eS2, eS3, eS4, qWT, qTYh, a2, Nat.add_zero]) <;>
            (try rfl) <;> omega)
  refine ⟨psum, hproc, ?_⟩
  dsimp only [psum]
  refine runs_start_le ?_
  refine runs_seq_triple_le hloop ⟨⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl⟩, rfl⟩ (fun st hI => ?_)
  obtain ⟨-, -, hfr, hsum⟩ := hI
  refine runs_ret_le (by eval_expr) (fun F' he => ?_) ?_
  · obtain rfl := PS.eq_of_args he
    exact ⟨hsum, hfr⟩
  · simp only [psumC, PS.args, List.getD_cons_zero, List.getD_cons_succ, Expr.size]
    have := Nat.mul_le_mul_left (F.hi - F.lo) (show 150 + 1 + 8 ≤ 100 + 100 by omega)
    omega

end MinCostFlow.LowStretch
