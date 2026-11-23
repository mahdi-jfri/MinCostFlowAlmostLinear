module

public import MinCostFlow.LSF.Program.FRMp
public import MinCostFlow.LSF.Program.FROwn
public import MinCostFlow.LSF.Program.FRRt
public import MinCostFlow.LSF.Program.AccLevel

/-!
# One level of the stretch sum

Level `i` uses the root set of the vertices whose depth in `T_H` is at most `i`
(`levelRoots`, `PathRoot.lean`). `levelStepProc` runs five passes:

1. `levelFlagProc` writes the flags `inR x = [thDep x ≤ i]`;
2. `frMpProc`, `frOwnProc` and `frRtProc` find the forest root `rt x` of every index
   (`FRMp.lean`, `FROwn.lean`, `FRRt.lean`);
3. `accLevelProc` adds the level's distance to the accumulator of each edge (`AccLevel.lean`).

The post gives the roots as an array `rt` with the rules of the three passes (`LevelRt`), so that
`rt_bridge` (`FRIdx.lean`) applies to it. The cost is `O(n + tM + m0 LB)`.
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.Num

@[expose] public section

/-! ## The flags -/

/-- Args: `[n, thDepPtr, inRPtr, i]`. Register `4` is the index `x`. -/
def levelFlagProc : Stmt :=
  forRange 4 (.const 0) (.reg 0)
    (.store (.bin .add (.reg 2) (.reg 4))
      (.bin .lt (.load (.bin .add (.reg 1) (.reg 4))) (.bin .add (.reg 3) (.const 1)))) ;;
  .ret (.const 0)

lemma levelFlagProc_noRand : levelFlagProc.NoRand := by
  simp [levelFlagProc, forRange, forUp, Stmt.NoRand]

/-- The flag of index `x` at level `i`. -/
def levelFlag (mem : ℕ → ℕ) (thDepPtr i x : ℕ) : ℕ :=
  if mem (thDepPtr + x) < i + 1 then 1 else 0

/-- The contract of `levelFlagProc`. -/
def levelFlagContract (w : ℕ) : Contract where
  pre args _ := ∃ n thDepPtr inRPtr i, args = [n, thDepPtr, inRPtr, i] ∧ 16 ≤ 2 ^ w ∧
    thDepPtr + n ≤ inRPtr ∧ inRPtr + n < 2 ^ w ∧ i + 1 < 2 ^ w
  post args mem ret mem' := ∃ n thDepPtr inRPtr i, args = [n, thDepPtr, inRPtr, i] ∧ ret = 0 ∧
    (∀ a, a < inRPtr ∨ inRPtr + n ≤ a → mem' a = mem a) ∧
    ∀ x < n, mem' (inRPtr + x) = levelFlag mem thDepPtr i x
  cost args _ := 30 * args.getD 0 0 + 20

theorem levelFlag_meetsContract {w : ℕ} {p : Program} {b : ℕ}
    (hp : p.procs[b]? = some levelFlagProc) :
    MeetsContract w p b (levelFlagContract w) := by
  classical
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  obtain ⟨n, thDepPtr, inRPtr, i, rfl, h16, hta, hiw, hi1⟩ := hpre
  have hw1 : 1 < 2 ^ w := by omega
  have hnw : n < 2 ^ w := by omega
  set args := [n, thDepPtr, inRPtr, i] with hargs
  let Inv : ℕ → State → Prop := fun j st =>
    st.regs 0 = n ∧ st.regs 1 = thDepPtr ∧ st.regs 2 = inRPtr ∧ st.regs 3 = i ∧
    st.regs 4 = j ∧ (∀ a, a < inRPtr ∨ inRPtr + j ≤ a → st.mem a = mem a) ∧
    ∀ x < j, st.mem (inRPtr + x) = levelFlag mem thDepPtr i x
  have hloop : Triple w p (fun st => st = startState args mem pos)
      (forRange 4 (.const 0) (.reg 0)
        (.store (.bin .add (.reg 2) (.reg 4))
          (.bin .lt (.load (.bin .add (.reg 1) (.reg 4))) (.bin .add (.reg 3) (.const 1)))))
      (normalPost (Inv n))
      (fun _ => (n - 0) * (15 + (Expr.reg 0).size + 8) +
        ((Expr.const 0).size + (Expr.reg 0).size + 5)) := by
    refine Triple.forRange_const 15 0 n (by omega) hw1 (fun _ => hnw) ?_ ?_ ?_ ?_
    · rintro st rfl
      refine ⟨by eval_expr, by simp [startState, hargs], by simp [startState, hargs],
        by simp [startState, hargs], by simp [startState, hargs], by simp, fun a _ => rfl,
        fun x hx => absurd hx (by omega)⟩
    · intro j st _ _ hI; exact hI.2.2.2.2.1
    · intro j st _ _ hI
      have r0 : st.regs 0 = n := hI.1
      eval_expr
    · intro j _ hjn st ω' hI
      obtain ⟨r0, r1, r2, r3, r4, hfr, hdone⟩ := hI
      have hm : st.mem (thDepPtr + j) = mem (thDepPtr + j) := hfr _ (Or.inl (by omega))
      refine runs_start_le ?_
      refine runs_store_le (x := inRPtr + j) (v := levelFlag mem thDepPtr i j) (by eval_expr)
        (by
          unfold levelFlag
          rw [← hm]
          eval_expr)
        ⟨⟨by simpa using r0, by simpa using r1, by simpa using r2, by simpa using r3, by simp,
          fun a ha => ?_, fun x hx => ?_⟩, by simpa using r4⟩ (by simp [Expr.size])
      · dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a (by omega)
      · dsimp only
        rcases Nat.lt_succ_iff_lt_or_eq.mp hx with hx | rfl
        · rw [Function.update_of_ne (by omega)]; exact hdone x hx
        · rw [Function.update_self]
  refine runs_start_le ?_
  unfold levelFlagProc
  refine runs_seq_triple_le hloop rfl ?_
  rintro st ⟨-, -, -, -, -, hfr, hdone⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨n, thDepPtr, inRPtr, i, rfl, rfl, hfr, hdone⟩ ?_
  simp only [levelFlagContract, hargs, List.getD_cons_zero, Expr.size_const, Expr.size_reg]
  omega

/-! ## The roots of one level -/

/-- The roots `rt` follow the rules of the three passes for the flags `inR`: there are arrays
`mp` and `own` with `MpRule`, `OwnState` and `RtRule`. -/
def LevelRt (n tM r : ℕ) (par pe piv inR rt : ℕ → ℕ) : Prop :=
  ∃ mp own : ℕ → ℕ,
    (∀ x < n, x ≠ r → mp x < tM ∧ MpRule inR par pe piv mp x) ∧
    OwnState r tM inR mp own n ∧ rt r = r ∧ ∀ x < n, x ≠ r → RtRule inR par pe own rt x

/-- The roots are indices. -/
lemma levelRt_lt {n tM r : ℕ} {tl hd par pe dep piv inR rt : ℕ → ℕ}
    (hR : RootedArrays n tM r tl hd par pe dep) (hr : r < n)
    (h : LevelRt n tM r par pe piv inR rt) : ∀ x < n, rt x < n := by
  obtain ⟨mp, own, -, hown, hrt_r, hrule⟩ := h
  suffices H : ∀ d, ∀ x < n, dep x = d → rt x < n from fun x hx => H _ x hx rfl
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
  intro x hx hd
  by_cases hxr : x = r
  · rw [hxr, hrt_r]; exact hr
  obtain ⟨hpe, -, hdep⟩ := hR.step x hx hxr
  rw [hrule x hx hxr]
  split_ifs with h1 h2
  · exact hx
  · exact ((hown _ hpe).1 h2).1
  · exact ih _ (by omega) _ (hR.par_lt x hx) rfl

end

end MinCostFlow.LSF.Program
