module

public import MinCostFlow.HierPaths.BuildProgInjectLayout
import MinCostFlow.HierPaths.BuildProgCutPack

/-!
# The request for one sibling pair

The two children have the same size. Write the two consecutive terminal
lists and the three offsets expected by the full router.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The arguments are the first terminal of each child, the common size,
and the output address. -/
def buildConnRequestProc : Stmt :=
  .seq (.store (.reg 3) (.const 0))
    (.seq (.store (.bin .add (.reg 3) (.const 1)) (.reg 2))
      (.seq (.store (.bin .add (.reg 3) (.const 2)) (.bin .add (.reg 2) (.reg 2)))
        (.seq (.assign 4 (.bin .add (.reg 3) (.const 3)))
          (.seq (.assign 5 (.bin .add (.reg 4) (.reg 2)))
            (.seq (forRange 6 (.const 0) (.reg 2)
              (.seq (.store (.bin .add (.reg 4) (.reg 6)) (.bin .add (.reg 0) (.reg 6)))
                (.store (.bin .add (.reg 5) (.reg 6)) (.bin .add (.reg 1) (.reg 6)))))
              (.ret (.bin .add (.reg 5) (.reg 2))))))))

theorem buildConnRequestProc_noRand : buildConnRequestProc.NoRand := by
  simp [buildConnRequestProc,forRange,forUp,Stmt.NoRand]

/-- One routing request with the terminals of the two sibling groups. -/
def connRequestPairs (a b s : ℕ) : List (Finset ℕ × Finset ℕ) :=
  [(shiftSet a (Finset.range s),shiftSet b (Finset.range s))]

/-- The procedure writes only the pair block. -/
def buildConnRequestContract (w : ℕ) : Contract where
  pre args _ := ∃ a b s out, args = [a,b,s,out] ∧
    a+s < 2^w ∧ b+s < 2^w ∧ out+3+2*s < 2^w
  post args mem v after := ∃ a b s out, args = [a,b,s,out] ∧
    v = out+3+2*s ∧ ListAt after out (pairsWords (connRequestPairs a b s)) ∧
    ∀ j, j < out ∨ v ≤ j → after j = mem j
  cost args _ := 48*(args.getD 2 0)+64

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The shifted range is written in its sorted order. -/
theorem finsetWords_shift_range (a s : ℕ) :
    finsetWords (shiftSet a (Finset.range s)) = tabList s (a+·) := by
  have hh := packedCutSide_one (s := s) (C := Finset.range s) (fun _ h => h) a
  have hf : ((List.range s).filter (fun j => decide ((if j ∈ Finset.range s then 1 else 0) = 1))) =
      List.range s := List.filter_eq_self.mpr (fun j hj => by simp [Finset.mem_range,List.mem_range.mp hj])
  rw [← hh]
  simp only [packedCutSide,hf,tabList]

/-- The pair block has exactly two arrays of the common size. -/
theorem connRequestPairs_words (a b s : ℕ) :
    pairsWords (connRequestPairs a b s) = [0,s,2*s] ++ tabList s (a+·) ++ tabList s (b+·) := by
  simp [pairsWords,connRequestPairs,finsetWords_shift_range,layoutList,csrList,csrOffsets,
    csrData,List.range_succ,length_tabList,Nat.two_mul]


/-- Packing a single router request costs linear time in the child size. -/
theorem buildConnRequestProc_meetsContract {w f : ℕ} {p : Program}
    (hf : p.procs[f]? = some buildConnRequestProc) :
    MeetsContract w p f (buildConnRequestContract w) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨a,b,s,out,rfl,ha,hb,hRoom⟩ := hPre
  let lo := out+3
  let hi := lo+s
  have hOne : 1 < 2^w := by omega
  have hTwo : 2 < 2^w := by omega
  have hThree : 3 < 2^w := by omega
  have hOut1 : out+1 < 2^w := by omega
  have hOut2 : out+2 < 2^w := by omega
  have hS2 : s+s < 2^w := by omega
  have hLo : lo < 2^w := by dsimp [lo]; omega
  have hHi : hi < 2^w := by dsimp [hi,lo]; omega
  let base := Function.update (Function.update (Function.update mem out 0) (out+1) s) (out+2) (s+s)
  let st₀ := startState [a,b,s,out] base pos
  let st₁ : State := {st₀ with regs := Function.update (Function.update st₀.regs 4 lo) 5 hi}
  let Inv := fun i (st : State) =>
    (∀ j < 6, st.regs j = st₁.regs j) ∧ st.regs 6 = i ∧
    (∀ j < i, st.mem (lo+j) = a+j ∧ st.mem (hi+j) = b+j) ∧
    ∀ j, (j < lo ∨ lo+i ≤ j ∧ j < hi ∨ hi+i ≤ j) → st.mem j = base j
  have hLoop := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 2)
    (body := .seq (.store (.bin .add (.reg 4) (.reg 6)) (.bin .add (.reg 0) (.reg 6)))
      (.store (.bin .add (.reg 5) (.reg 6)) (.bin .add (.reg 1) (.reg 6))))
    (P := fun st => st = st₁) (Inv := Inv) 18 0 s (Nat.zero_le _) hOne
    (fun _ => by omega)
    (fun st he => by
      subst st
      refine ⟨Expr.eval_const (Nat.two_pow_pos _),?_,by simp,fun _ hj => False.elim (Nat.not_lt_zero _ hj),
        fun _ _ => rfl⟩
      intro j hj
      exact Function.update_of_ne (by omega) ..)
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq (h.1 2 (by decide))) ?_
  swap
  · intro i _ hs st ω ⟨hr,hc,hOld,hFrame⟩
    have h0 : st.regs 0 = a := hr 0 (by decide)
    have h1 : st.regs 1 = b := hr 1 (by decide)
    have h4 : st.regs 4 = lo := hr 4 (by decide)
    have h5 : st.regs 5 = hi := hr 5 (by decide)
    have ha' : a+i < 2^w := by omega
    have hb' : b+i < 2^w := by omega
    have hLo' : lo+i < 2^w := by dsimp [lo]; omega
    have hHi' : hi+i < 2^w := by dsimp [hi,lo]; omega
    have hSep : lo+i < hi := by dsimp [hi]; omega
    refine runs_start_le ?_
    refine runs_seq_store_le (x := lo+i) (v := a+i) ?_ ?_ ?_
    · exact Expr.eval_add (Expr.eval_reg_of_eq h4) (Expr.eval_reg_of_eq hc) hLo'
    · exact Expr.eval_add (Expr.eval_reg_of_eq h0) (Expr.eval_reg_of_eq hc) ha'
    refine runs_store_le (x := hi+i) (v := b+i) ?_ ?_ ?_ ?_
    · exact Expr.eval_add (Expr.eval_reg_of_eq h5) (Expr.eval_reg_of_eq hc) hHi'
    · exact Expr.eval_add (Expr.eval_reg_of_eq h1) (Expr.eval_reg_of_eq hc) hb'
    · let next := Function.update (Function.update st.mem (lo+i) (a+i)) (hi+i) (b+i)
      refine ⟨⟨fun j hj => (Function.update_of_ne (by omega) ..).trans (hr j hj),by simp,?_,?_⟩,hc⟩
      · intro j hj
        change next (lo+j) = a+j ∧ next (hi+j) = b+j
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · obtain ⟨hL,hH⟩ := hOld j hj
          exact ⟨(Function.update_of_ne (by omega) ..).trans ((Function.update_of_ne (by omega) ..).trans hL),
            (Function.update_of_ne (by omega) ..).trans ((Function.update_of_ne (by omega) ..).trans hH)⟩
        · simp only [next,Function.update_of_ne (show lo+j ≠ hi+j by omega),Function.update_self,and_self]
      · intro j hj
        change next j = base j
        exact (Function.update_of_ne (by omega) ..).trans
          ((Function.update_of_ne (by omega) ..).trans (hFrame j (by omega)))
    · simp [Expr.size]
  refine runs_start_le ?_
  unfold buildConnRequestProc
  refine runs_seq_store_le (x := out) (v := 0) (by rfl) (Expr.eval_const (Nat.two_pow_pos _)) ?_
  refine runs_seq_store_le (x := out+1) (v := s) ?_ (by rfl) ?_
  · simp [Expr.eval,startState,hOne,hOut1]
  refine runs_seq_store_le (x := out+2) (v := s+s) ?_ ?_ ?_
  · simp [Expr.eval,startState,hTwo,hOut2]
  · simp [Expr.eval,startState,hS2]
  refine runs_seq_assign_le (v := lo) ?_ ?_
  · simp [Expr.eval,startState,hThree,hLo,lo]
  refine runs_seq_assign_le (v := hi) ?_ ?_
  · simp [Expr.eval,startState,Function.update,hHi,hi]
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨hr,_,hLists,hFrame⟩
  have hTop : hi+s = out+3+2*s := by dsimp [hi,lo]; omega
  refine runs_ret_le (v := out+3+2*s) ?_ ?_ ?_
  · rw [← hTop]
    exact Expr.eval_add (Expr.eval_reg_of_eq (hr 5 (by decide)))
      (Expr.eval_reg_of_eq (hr 2 (by decide))) (hTop.symm ▸ hRoom)
  · refine ⟨a,b,s,out,rfl,rfl,?_,?_⟩
    · rw [connRequestPairs_words, List.append_assoc]
      apply listAt_append.mpr
      refine ⟨?_,?_⟩
      · intro j hj
        have hr : j = 0 ∨ j = 1 ∨ j = 2 := by simp at hj; omega
        have hL : out+j < lo := by dsimp [lo]; rcases hr with rfl|rfl|rfl <;> omega
        rw [hFrame _ (Or.inl hL)]
        rcases hr with rfl|rfl|rfl
        · change base out = 0
          simp [base]
        · change base (out+1) = s
          simp [base]
        · change base (out+2) = 2*s
          simp [base,Nat.two_mul]
      · change ListAt st.mem lo (tabList s (a+·) ++ tabList s (b+·))
        apply listAt_append.mpr
        rw [length_tabList]
        constructor
        · intro j hj
          rw [length_tabList] at hj
          exact ((hLists j hj).1).trans (by simp [tabList])
        · intro j hj
          rw [length_tabList] at hj
          exact ((hLists j hj).2).trans (by simp [tabList])
    · intro j hj
      change j < out ∨ out+3+2*s ≤ j at hj
      have hh : j < lo ∨ lo+s ≤ j ∧ j < hi ∨ hi+s ≤ j := by
        rw [hTop]
        dsimp [lo]
        omega
      exact (hFrame j hh).trans (by
        simp only [base,Function.update_of_ne (show j ≠ out+2 by omega),
          Function.update_of_ne (show j ≠ out+1 by omega),Function.update_of_ne (show j ≠ out by omega)])
  · simp [buildConnRequestContract,Expr.size]
    omega

end MinCostFlow.HierPaths
