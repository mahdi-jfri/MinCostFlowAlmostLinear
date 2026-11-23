module

public import MinCostFlow.LowStretch.ProgChildTopW
public import MinCostFlow.LowStretch.ProgAmort

/-!
# The top level: the loop over the children

The loop of the top level calls `oneP` for `k = 0, 1, …, nch - 1`, with the record block of
child `k` at `h + 9k` and the heap pointer in register `26`. Its invariant is `CInv` before
child `k`; the run of one child (`CS.oneP_runs`) moves it to `k + 1`. The words that `oneP_runs`
asks for follow from `CS.top_room`. So the loop ends with `CInv` after the last child, within
`Σ (costK k + 100)` (`CS.topLoop_runs`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

namespace CS

variable {S : CS} {w : ℕ} {M1 : ℕ → ℕ}

/-- The state of the loop before child `k`. -/
def LoopInv (w : ℕ) (S : CS) (M1 : ℕ → ℕ) (k : ℕ) (st : State) : Prop :=
  k ≤ S.nch ∧ (∀ r < 25, st.regs r = S.topF r) ∧ st.regs 25 = k ∧
    ∃ H Rs, st.regs 26 = H ∧ CInv w S M1 k H Rs st.mem

/-- The cost still to come before child `k`. -/
noncomputable def loopRem (S : CS) (M1 : ℕ → ℕ) (k : ℕ) : ℕ :=
  ∑ j ∈ Finset.Ico k S.nch, (S.costK M1 j + 100) + 10

theorem loopRem_succ {k : ℕ} (hk : k < S.nch) :
    S.loopRem M1 k = S.costK M1 k + 100 + S.loopRem M1 (k + 1) := by
  unfold loopRem
  rw [Finset.sum_eq_sum_Ico_succ_bot hk]
  omega

/-- The words that the run of child `k` asks for. -/
theorem child_words (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) {k H : ℕ} {Rs : ℕ → Rec} {M : ℕ → ℕ} (hI : CInv w S M1 k H Rs M)
    (hk : k < S.nch) :
    H + S.spaceK M1 k + 2 < 2 ^ w ∧
      drawEnd (S.dwE M1 k H) + 3 * (S.sNK M1 k + S.T.N + 1) < 2 ^ w := by
  have h1 := hI.hspace
  have h2 := top_room hpre M1
  have h3 : ∑ j ∈ Finset.range (k + 1), S.spaceK M1 j ≤ ∑ j ∈ Finset.range S.nch, S.spaceK M1 j :=
    Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
  rw [Finset.sum_range_succ] at h3
  have h4 := drawEnd_le (H := H) hpre hT hk
  have h5 : S.sNK M1 k ≤ ∑ j ∈ Finset.range S.nch, S.sNK M1 j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hk)
  have h6 := sum_sNK_le (S := S) M1
  constructor <;> omega

/-- **The loop over the children.** -/
theorem topLoop_runs {p : Program} {ω : ℕ → Bool} {I : CIdx}
    (fone : p.procs[I.one]? = some (oneP I))
    (fhw : MeetsContract w p I.hw (hwC w)) (fpc : MeetsContract w p I.pc (pcC w))
    (fnc : MeetsContract w p I.nc (ncC w)) (fsm : MeetsContract w p I.sm (smC w))
    (fdr : MeetsContract w p I.dr (drawC w)) (frs : p.procs[I.rs]? = some (rsP I))
    (flg : MeetsContract w p I.lg (log2C w)) (fsp : MeetsContract w p I.sp (splitC w))
    (fio : MeetsContract w p I.io (iotaC w)) (fgc : MeetsContract w p I.gc (grpCopyC w))
    (hpre : ChildPre w S.T S.G S.P S.c S.R S.D S.GB S.RB S.XB S.h S.mem)
    (hT : TopOk S M1) {st : State} (hI : S.LoopInv w M1 0 st) :
    ∃ o st' c, Runs w p ω (topLoop I) st o st' c ∧ o = .normal ∧
      (∃ H Rs, st'.regs 26 = H ∧ CInv w S M1 S.nch H Rs st'.mem) ∧ S.loopRem M1 0 ≥ c := by
  have hw : S.H0 + S.nch + 4 < 2 ^ w := by have := top_room hpre M1; omega
  have hF := topF_lt hpre hw
  have hw1 : 10 < 2 ^ w := by have := top_room hpre M1; omega
  have e1 : (Expr.bin .lt (.reg 25) (.reg 4)).size = 3 := rfl
  have hstep : ∀ (k : ℕ) (st : State), S.LoopInv w M1 k st →
      (if st.regs 25 < S.nch then 1 else 0) ≠ 0 →
      ∃ o st₁ c₁, Runs w p ω (.seq (.assign 27 (.bin .add (.reg 3) (mulC 9 25)))
        (.seq (.call 26 I.one (rgs [0, 1, 2, 27, 25, 26, 8, 10, 12, 14, 15]))
          (.assign 25 (.bin .add (.reg 25) (.const 1))))) st o st₁ c₁ ∧
        (o = .normal ∧ S.LoopInv w M1 (k + 1) st₁) ∧
          3 + S.loopRem M1 (k + 1) + 1 + c₁ ≤ S.loopRem M1 k := by
    intro k st h h0
    obtain ⟨hk, hR, h25, H, Rs, h26, hI⟩ := h
    have hk' : k < S.nch := by
      have : st.regs 25 < S.nch := by
        by_contra hc
        exact h0 (by simp only [hc, if_false])
      omega
    obtain ⟨hr1, hr2⟩ := child_words hpre hT hI hk'
    have hsucc := loopRem_succ (S := S) (M1 := M1) hk'
    have g0 : st.regs 0 = S.GB := hR 0 (by norm_num)
    have g1 : st.regs 1 = S.RB := hR 1 (by norm_num)
    have g2 : st.regs 2 = S.XB := hR 2 (by norm_num)
    have g3 : st.regs 3 = S.h := hR 3 (by norm_num)
    have g8 : st.regs 8 = S.OFFN := hR 8 (by norm_num)
    have g10 : st.regs 10 = S.ORDN := hR 10 (by norm_num)
    have g12 : st.regs 12 = S.OFFK := hR 12 (by norm_num)
    have g14 : st.regs 14 = S.ORDK := hR 14 (by norm_num)
    have g15 : st.regs 15 = S.HM := hR 15 (by norm_num)
    have hCHX : S.h + 9 * k ≤ S.CHX := by have := S.lay.1; omega
    have hb : S.CHX < 2 ^ w := hF 7
    -- the body: the block address, the call, the counter
    refine runs_seq_assign_le (v := S.h + 9 * k)
      (Expr.eval_add (Expr.eval_reg_of_eq g3) (Expr.eval_mul (Expr.eval_const (by omega))
        (Expr.eval_reg_of_eq h25) (by omega)) (by omega)) ?_
    set st₀ : State := { st with regs := Function.update st.regs 27 (S.h + 9 * k) }
    have hargs : evalArgs w st₀ (rgs [0, 1, 2, 27, 25, 26, 8, 10, 12, 14, 15]) =
        some (S.oneV M1 k H).args := by
      rw [evalArgs_rgs]
      simp only [st₀, List.map_cons, List.map_nil, Function.update_apply]
      simp only [show (0 : ℕ) ≠ 27 by decide, show (1 : ℕ) ≠ 27 by decide,
        show (2 : ℕ) ≠ 27 by decide, show (25 : ℕ) ≠ 27 by decide, show (26 : ℕ) ≠ 27 by decide,
        show (8 : ℕ) ≠ 27 by decide, show (10 : ℕ) ≠ 27 by decide, show (12 : ℕ) ≠ 27 by decide,
        show (14 : ℕ) ≠ 27 by decide, show (15 : ℕ) ≠ 27 by decide, if_false, if_true,
        g0, g1, g2, g8, g10, g12, g14, g15, h25, h26]
      rfl
    obtain ⟨o₁, st₁, c₁, hrun, ⟨H', R', rfl, hI'⟩, hc₁⟩ := oneP_runs (p := p) (ω := ω) (I := I)
      fhw fpc fnc fsm fdr frs flg fsp fio fgc hpre hT hI hk' hr1 hr2 st₀.pos
    refine runs_seq_callB_le hargs fone hrun ?_
    refine runs_assign_le (v := k + 1) (Expr.eval_add (Expr.eval_reg_of_eq ?_)
      (Expr.eval_const (by omega)) (by omega)) ⟨rfl, by omega, fun r hr => ?_, ?_, H', _, ?_, hI'⟩ ?_
    · show Function.update st.regs 27 (S.h + 9 * k) 25 = k
      rw [Function.update_of_ne (by decide)]; exact h25
    · show Function.update (Function.update (Function.update st.regs 27 (S.h + 9 * k)) 26 H') 25
        (k + 1) r = _
      rw [Function.update_of_ne (by omega), Function.update_of_ne (by omega),
        Function.update_of_ne (by omega)]
      exact hR r hr
    · show Function.update (Function.update (Function.update st.regs 27 (S.h + 9 * k)) 26 H') 25
        (k + 1) 25 = k + 1
      exact Function.update_self ..
    · show Function.update (Function.update (Function.update st.regs 27 (S.h + 9 * k)) 26 H') 25
        (k + 1) 26 = H'
      rw [Function.update_of_ne (by decide)]
      exact Function.update_self ..
    · have s1 : (Expr.bin .add (.reg 3) (mulC 9 25)).size ≤ 10 := by decide
      have s2 : argsSize (rgs [0, 1, 2, 27, 25, 26, 8, 10, 12, 14, 15]) ≤ 30 := by decide
      have s3 : (Expr.bin .add (.reg 25) (.const 1)).size ≤ 10 := by decide
      omega
  obtain ⟨o, st', c, hr, r, ⟨ho, -, hfin⟩, hc⟩ := runs_loop_amort (p := p) (ω := ω)
    (Inv := S.LoopInv w M1)
    (Fin := fun o st r => o = .normal ∧ r = 0 ∧
      ∃ H Rs, st.regs 26 = H ∧ CInv w S M1 S.nch H Rs st.mem)
    (fun k => S.nch - k) (S.loopRem M1)
    (condVal := fun st => if st.regs 25 < S.nch then 1 else 0)
    (fun k st h => Expr.eval_lt_op (w := w) (Expr.eval_reg_of_eq rfl)
      (Expr.eval_reg_of_eq (h.2.1 4 (by norm_num))) (by omega))
    (fun k st h h0 => by
      obtain ⟨hk, -, h25, H, Rs, h26, hI⟩ := h
      have hkn : k = S.nch := by
        have : ¬ st.regs 25 < S.nch := fun hc => by simp only [hc, ite_true] at h0; exact absurd h0 (by decide)
        omega
      subst hkn
      refine ⟨0, ⟨rfl, rfl, H, Rs, h26, hI⟩, ?_⟩
      rw [e1]
      unfold loopRem
      simp)
    (fun k st h h0 => by
      obtain ⟨o, st₁, c₁, h1, ⟨rfl, h2⟩, h3⟩ := hstep k st h h0
      have := h2.1
      exact ⟨.normal, st₁, c₁, h1, k + 1, h2, by omega, by rw [e1]; omega⟩) 0 st hI
  subst ho
  exact ⟨_, st', c, hr, rfl, hfin, by omega⟩

end CS

end MinCostFlow.LowStretch
