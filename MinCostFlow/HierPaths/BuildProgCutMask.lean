module

public import MinCostFlow.HierPaths.BuildProgCutPack

/-!
# From the core's vertex list to a membership mask

Initialize every child bit to the default value, then flip the bits of the vertices
in the core's set. A default of zero selects the set. A default of one selects
the complement. The source list is retained for later use.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- Args are the list base and length, the mask base and length, and the default bit. -/
def buildCutMaskProc : Stmt :=
  .seq (forRange 5 (.const 0) (.reg 3)
      (.store (.bin .add (.reg 2) (.reg 5)) (.reg 4)))
    (.seq (forRange 5 (.const 0) (.reg 1)
      (.store (.bin .add (.reg 2) (.load (.bin .add (.reg 0) (.reg 5))))
        (.bin .sub (.const 1) (.reg 4)))) (.ret (.const 0)))

/-- The mask fits and is above the core's set. Each vertex in the core's set is a valid
local vertex. The default chooses the side used for padding or injection. -/
def buildCutMaskContract (w s : ℕ) (U : Finset ℕ) : Contract where
  pre args mem := ∃ src base flip, args = [src, U.card, base, s, flip] ∧
    ListAt mem src (finsetWords U) ∧ U ⊆ Finset.range s ∧
    src + U.card ≤ base ∧ base + s < 2 ^ w ∧ 1 < 2 ^ w ∧ flip ≤ 1
  post args mem _ mem' := ∃ src base flip, args = [src, U.card, base, s, flip] ∧
    (∀ i < s, mem' (base + i) = if i ∈ U then 1 - flip else flip) ∧
    ∀ j, (j < base ∨ base + s ≤ j) → mem' j = mem j
  cost _ _ := 20 * (s + U.card) + 32

theorem buildCutMaskProc_noRand : buildCutMaskProc.NoRand := by
  simp [buildCutMaskProc, forRange, forUp, Stmt.NoRand]

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

private def maskFrame (mem : ℕ → ℕ) (base stop : ℕ) (st : State) : Prop :=
    ∀ j, (j < base ∨ base + stop ≤ j) → st.mem j = mem j

private def maskRegs (src n base s flip : ℕ) (st : State) : Prop :=
  st.regs 0 = src ∧ st.regs 1 = n ∧ st.regs 2 = base ∧ st.regs 3 = s ∧ st.regs 4 = flip

private theorem buildMaskFill_triple {w src n base s flip : ℕ} {mem : ℕ → ℕ} (p : Program)
    (hEnd : base + s < 2 ^ w) (hWord : 1 < 2 ^ w) :
    Triple w p (fun st => maskRegs src n base s flip st ∧ st.mem = mem)
      (forRange 5 (.const 0) (.reg 3) (.store (.bin .add (.reg 2) (.reg 5)) (.reg 4)))
      (normalPost fun st => maskRegs src n base s flip st ∧
        (∀ j < s, st.mem (base + j) = flip) ∧ maskFrame mem base s st)
      (fun _ => 16 * s + 7) := by
  let Inv := fun i st => maskRegs src n base s flip st ∧ st.regs 5 = i ∧
    (∀ j < i, st.mem (base + j) = flip) ∧ maskFrame mem base i st
  have hLoop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 3)
    (body := .store (.bin .add (.reg 2) (.reg 5)) (.reg 4))
    (P := fun st => maskRegs src n base s flip st ∧ st.mem = mem) (Inv := Inv)
    5 0 s (Nat.zero_le _) hWord (fun _ => by omega)
    (fun st ⟨hrs, hm⟩ => by
      refine ⟨Expr.eval_const (Nat.two_pow_pos _), ?_⟩
      exact ⟨hrs, by simp, fun j hj => False.elim (Nat.not_lt_zero j hj),
        fun _ _ => congrFun hm _⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.1.2.2.2.1)
    (fun i _ hi => by
      intro st ω ⟨hrs, h5, hz, hf⟩
      have ha : base + i < 2 ^ w := by omega
      refine ⟨.normal, { st with mem := Function.update st.mem (base + i) flip },
        5, runs_store_iff.mpr ⟨base + i, flip, ?_, Expr.eval_reg_of_eq hrs.2.2.2.2, rfl, rfl, by simp⟩,
        ⟨⟨hrs, by simp, ?_, ?_⟩, h5⟩, by simp⟩
      · exact Expr.eval_add (Expr.eval_reg_of_eq hrs.2.2.1) (Expr.eval_reg_of_eq h5) ha
      · intro j hj
        change Function.update st.mem (base + i) flip (base + j) = _
        by_cases hji : j = i
        · subst j; simp
        · rw [Function.update_of_ne (by omega)]
          exact hz j (by omega)
      · intro j hj
        change Function.update st.mem (base + i) flip j = mem j
        rw [Function.update_of_ne (by omega)]
        exact hf j (by omega))
  refine hLoop.conseq (fun _ h => h) ?_ ?_
  · intro o st hPost
    cases o with
    | returned _ => exact False.elim hPost
    | normal => exact ⟨hPost.1, hPost.2.2⟩
  · intro _ _; simp [Expr.size]; omega

private theorem buildMaskToggle_triple {w src base s flip : ℕ} {vs : List ℕ} {mem : ℕ → ℕ}
    (p : Program) (hVs : ListAt mem src vs)
    (hLocal : ∀ v ∈ vs, v < s) (hSep : src + vs.length ≤ base)
    (hEnd : base + s < 2 ^ w) (hWord : 1 < 2 ^ w) :
    Triple w p (fun st => maskRegs src vs.length base s flip st ∧
      (∀ j < s, st.mem (base + j) = flip) ∧ maskFrame mem base s st)
      (forRange 5 (.const 0) (.reg 1)
        (.store (.bin .add (.reg 2) (.load (.bin .add (.reg 0) (.reg 5))))
          (.bin .sub (.const 1) (.reg 4))))
      (normalPost fun st =>
        (∀ j < s, st.mem (base + j) = if j ∈ vs then 1 - flip else flip) ∧
        maskFrame mem base s st)
      (fun _ => 20 * vs.length + 7) := by
  let Inv := fun i st => maskRegs src vs.length base s flip st ∧ st.regs 5 = i ∧
    (∀ j < s, st.mem (base + j) = if j ∈ vs.take i then 1 - flip else flip) ∧
    maskFrame mem base s st
  have hLoop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 2) (.load (.bin .add (.reg 0) (.reg 5))))
      (.bin .sub (.const 1) (.reg 4)))
    (P := fun st => maskRegs src vs.length base s flip st ∧
      (∀ j < s, st.mem (base + j) = flip) ∧ maskFrame mem base s st)
    (Inv := Inv) 10 0 vs.length (Nat.zero_le _) hWord (fun _ => by omega)
    (fun st ⟨hrs, hm, hf⟩ => by
      exact ⟨Expr.eval_const (Nat.two_pow_pos _), hrs, by simp, by simpa using hm, hf⟩)
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.1.2.1)
    (fun i _ hi => by
      intro st ω ⟨hrs, h5, hz, hf⟩
      let v := vs[i]
      have hv : v < s := hLocal v (List.getElem_mem hi)
      have ha : base + v < 2 ^ w := by omega
      have hiw : src + i < 2 ^ w := by omega
      have hRead : st.mem (src + i) = v := (hf _ (Or.inl (by omega))).trans (hVs i hi)
      have hTake : vs.take (i + 1) = vs.take i ++ [v] := List.take_succ_eq_append_getElem hi
      refine ⟨.normal, { st with mem := Function.update st.mem (base + v) (1 - flip) },
        10, runs_store_iff.mpr ⟨base + v, 1 - flip, ?_, ?_, rfl, rfl, by simp⟩,
        ⟨⟨hrs, by simp, ?_, ?_⟩, h5⟩, by simp⟩
      · exact Expr.eval_add (Expr.eval_reg_of_eq hrs.2.2.1)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq hrs.1)
            (Expr.eval_reg_of_eq h5) hiw) hRead) ha
      · exact Expr.eval_sub (Expr.eval_const hWord) (Expr.eval_reg_of_eq hrs.2.2.2.2) hWord
      · intro j hj
        change Function.update st.mem (base + v) (1 - flip) (base + j) =
          if j ∈ vs.take (i + 1) then 1 - flip else flip
        rw [hTake]
        by_cases h : j = v
        · subst j; simp
        · rw [Function.update_of_ne (by omega)]
          simpa [h] using hz j hj
      · intro j hj
        change Function.update st.mem (base + v) (1 - flip) j = mem j
        rw [Function.update_of_ne (by omega)]
        exact hf j hj)
  refine hLoop.conseq (fun _ h => h) ?_ ?_
  · intro o st hPost
    cases o with
    | returned _ => exact False.elim hPost
    | normal =>
      refine ⟨?_, hPost.2.2.2⟩
      simpa using hPost.2.2.1
  · intro _ _; simp [Expr.size]; omega

/-- The mask builder runs in time linear in the child size plus the returned set size. -/
theorem buildCutMaskProc_meetsContract {w s : ℕ} {U : Finset ℕ} {p : Program} {f : ℕ}
    (hf : p.procs[f]? = some buildCutMaskProc) :
    MeetsContract w p f (buildCutMaskContract w s U) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨src, base, flip, rfl, hAt, hLocal, hSep, hEnd, hWord, _⟩ := hPre
  have hLen : (finsetWords U).length = U.card := Finset.length_sort _
  have hVl : ∀ v ∈ finsetWords U, v < s := fun v hv =>
    Finset.mem_range.mp (hLocal ((Finset.mem_sort _).mp hv))
  refine runs_start_le ?_
  unfold buildCutMaskProc
  refine runs_seq_triple_le (buildMaskFill_triple (src := src) (n := U.card) (flip := flip) p hEnd hWord)
    ⟨⟨rfl, rfl, rfl, rfl, rfl⟩, rfl⟩ ?_
  intro st ⟨hR, hM, hF⟩
  refine runs_seq_triple_le (buildMaskToggle_triple p hAt hVl (by rwa [hLen]) hEnd hWord)
    ⟨by simpa only [hLen] using hR, hM, hF⟩ ?_
  intro _ ⟨hz, hFrame⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _))
    ⟨src, base, flip, rfl, by simpa [finsetWords] using hz, hFrame⟩ ?_
  simp [buildCutMaskContract, hLen, Expr.size]
  omega

end MinCostFlow.HierPaths
