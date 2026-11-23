module

public import MinCostFlow.HierPaths.BuildProgGameSelect

/-!
# Keeping only the requesting children for the next round

The cut index list is in scan order. Its `i`-th index is at least `i`,
so forwarding the selected entries into the first cells of an active
array does not overwrite an entry before that entry is read.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The next active array, in the common router's matching order. -/
def activeCompactWords (old idxs : List ℕ) : List ℕ :=
  idxs.map fun i => old.getD i 0

/-- Args `[base, indices, count]`. Compact the array at `base` in place. -/
def buildActiveCompactProc : Stmt :=
  .seq (forRange 3 (.const 0) (.reg 2)
      (.store (.bin .add (.reg 0) (.reg 3))
        (.load (.bin .add (.reg 0) (.load (.bin .add (.reg 1) (.reg 3)))))))
    (.ret (.const 0))

/-- The index table lies above the original active array and every selected index
is at or after its destination. -/
def buildActiveCompactContract (w : ℕ) (old idxs : List ℕ) : Contract where
  pre args mem := ∃ base cuts, args = [base,cuts,idxs.length] ∧
    ListAt mem base old ∧ ListAt mem cuts idxs ∧
    base + old.length ≤ cuts ∧ cuts + idxs.length < 2 ^ w ∧ 1 < 2 ^ w ∧
    ∀ i (hi : i < idxs.length), i ≤ idxs[i] ∧ idxs[i] < old.length
  post args mem _ mem' := ∃ base cuts, args = [base,cuts,idxs.length] ∧
    ListAt mem' base (activeCompactWords old idxs) ∧
    ∀ a, (a < base ∨ base + idxs.length ≤ a) → mem' a = mem a
  cost _ _ := 24 * idxs.length + 16

theorem buildActiveCompactProc_noRand : buildActiveCompactProc.NoRand := by
  simp [buildActiveCompactProc, forRange, forUp, Stmt.NoRand]

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The compaction keeps precisely the entries at the selected indices. -/
theorem buildActiveCompactProc_meetsContract {w f : ℕ} {p : Program} {old idxs : List ℕ}
    (hf : p.procs[f]? = some buildActiveCompactProc) :
    MeetsContract w p f (buildActiveCompactContract w old idxs) := by
  refine meetsContract_of_runs hf fun args mem pos ω _ hPre => ?_
  obtain ⟨base,cuts,rfl,hOld,hIdx,hSep,hFit,hw,hChosen⟩ := hPre
  let Inv := fun (i : ℕ) (st : State) =>
    st.regs 0 = base ∧ st.regs 1 = cuts ∧ st.regs 2 = idxs.length ∧ st.regs 3 = i ∧
    (∀ j (hj : j < idxs.length), j < i → st.mem (base + j) = old.getD idxs[j] 0) ∧
    (∀ a, (a < base ∨ base + i ≤ a) → st.mem a = mem a)
  have hLoop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.reg 0) (.reg 3))
      (.load (.bin .add (.reg 0) (.load (.bin .add (.reg 1) (.reg 3))))))
    (P := fun st => st = startState [base,cuts,idxs.length] mem pos)
    (Inv := Inv) 12 0 idxs.length (Nat.zero_le _) hw (fun _ => by omega)
    (fun st he => by
      subst st
      exact ⟨Expr.eval_const (Nat.two_pow_pos _),rfl,rfl,rfl,rfl,
        fun j _ hj => False.elim (Nat.not_lt_zero j hj),fun _ _ => rfl⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq h.2.2.1) ?_
  swap
  · intro i _ hi st ω ⟨h0,h1,h2,h3,hDone,hFrame⟩
    let j := idxs[i]
    obtain ⟨hij,hj⟩ := hChosen i hi
    change i ≤ j at hij
    change j < old.length at hj
    have hIdxAt : st.mem (cuts + i) = j :=
      (hFrame _ (Or.inr (by omega))).trans (hIdx i hi)
    have hOldAt : st.mem (base + j) = old.getD j 0 := by
      rw [hFrame _ (Or.inr (by omega)), hOld j hj, List.getD_eq_getElem _ _ hj]
    have hci : cuts + i < 2 ^ w := by omega
    have hbj : base + j < 2 ^ w := by omega
    have hbi : base + i < 2 ^ w := by omega
    refine ⟨.normal,{st with mem := Function.update st.mem (base + i) (old.getD j 0)},11,?_,?_,?_⟩
    · apply runs_store_iff.mpr
      exact ⟨base+i,old.getD j 0,
        Expr.eval_add (Expr.eval_reg_of_eq h0) (Expr.eval_reg_of_eq h3) hbi,
        Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h0)
          (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h1) (Expr.eval_reg_of_eq h3) hci)
            hIdxAt) hbj) hOldAt,rfl,rfl,rfl⟩
    · refine ⟨⟨by simpa using h0,by simpa using h1,by simpa using h2,by simp,?_,?_⟩,h3⟩
      · intro t ht hti
        change Function.update st.mem (base + i) (old.getD j 0) (base + t) = _
        by_cases he : t = i
        · subst t
          simp [j]
        · rw [Function.update_of_ne (by omega)]
          exact hDone t ht (by omega)
      · intro a ha
        change Function.update st.mem (base + i) (old.getD j 0) a = mem a
        rw [Function.update_of_ne (by omega)]
        exact hFrame a (by omega)
    · simp
  refine runs_start_le ?_
  unfold buildActiveCompactProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_,_,_,_,hDone,hFrame⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _)) ⟨base,cuts,rfl,?_,hFrame⟩ ?_
  · intro j hj
    have hp : j < idxs.length := by simpa [activeCompactWords] using hj
    simpa only [activeCompactWords,List.getElem_map] using hDone j hp hp
  · simp [buildActiveCompactContract,Expr.size]
    omega

end MinCostFlow.HierPaths
