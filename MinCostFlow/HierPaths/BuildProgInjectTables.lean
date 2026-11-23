module

public import MinCostFlow.HierPaths.BuildProgChoiceHistory

/-!
# The injection's child tables

The play scans the active table in a changing order. The injection
instead visits each original child once. Write its index, graph pointer
and terminal offset in three consecutive tables.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- Write the graph address, terminal offset and original child index. -/
def buildInjectTablesStep : Stmt :=
  .seq (.assign 9 (.bin .add (.reg 2) (.bin .mul (.reg 8) (.reg 6))))
    (.seq (.store (.bin .add (.reg 0) (.reg 8)) (.reg 9))
      (.seq (.store (.bin .add (.reg 1) (.reg 8))
          (.bin .add (.reg 3) (.bin .mul (.reg 8) (.reg 4))))
        (.store (.bin .add (.reg 7) (.reg 8)) (.reg 8))))

/-- Args are graph pointers, terminal offsets, first graph slot, first
terminal, child size, number of children, the size of one slot, and the index table. -/
def buildInjectTablesProc : Stmt :=
  .seq (forRange 8 (.const 0) (.reg 5) buildInjectTablesStep) (.ret (.const 0))

theorem buildInjectTablesProc_noRand : buildInjectTablesProc.NoRand := by
  simp [buildInjectTablesProc,buildInjectTablesStep,forRange,forUp,Stmt.NoRand]

/-- The written prefixes and the frame outside the three regions. -/
def InjectTablesAt (mem after : ℕ → ℕ) (graphs offsets slots first s span n idx : ℕ) : Prop :=
  (∀ i < n, after (graphs+i) = slots+i*span ∧ after (offsets+i) = first+i*s ∧
    after (idx+i) = i) ∧
  ∀ a, (a < graphs ∨ graphs+n ≤ a) → (a < offsets ∨ offsets+n ≤ a) →
    (a < idx ∨ idx+n ≤ a) → after a = mem a

/-- The scan writes three tables and preserves all graph blocks. -/
def buildInjectTablesContract (w : ℕ) : Contract where
  pre args _ := ∃ graphs offsets slots first s k span idx,
    args = [graphs,offsets,slots,first,s,k,span,idx] ∧
    graphs+k ≤ offsets ∧ offsets+k ≤ idx ∧ idx+k < 2^w ∧
    slots+k*span < 2^w ∧ first+k*s < 2^w ∧ 1 < 2^w
  post args mem _ after := ∃ graphs offsets slots first s k span idx,
    args = [graphs,offsets,slots,first,s,k,span,idx] ∧
    InjectTablesAt mem after graphs offsets slots first s span k idx ∧
    ListAt after graphs (tabList k (fun i => slots+i*span)) ∧
    ListAt after offsets (tabList k (fun i => first+i*s)) ∧
    ListAt after idx (List.range k)
  cost args _ := 60*(args.getD 5 0)+16

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The scan writes exactly three words per original child. -/
theorem buildInjectTablesProc_meetsContract {w f : ℕ} {p : Program}
    (hf : p.procs[f]? = some buildInjectTablesProc) :
    MeetsContract w p f (buildInjectTablesContract w) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨graphs,offsets,slots,first,s,k,span,idx,rfl,hG,hO,hIdx,hWord,hTerm,hw⟩ := hPre
  let st₀ := startState [graphs,offsets,slots,first,s,k,span,idx] mem pos
  let Inv := fun i (st : State) =>
    (∀ j < 9, j ≠ 8 → st.regs j = st₀.regs j) ∧ st.regs 8 = i ∧
      InjectTablesAt mem st.mem graphs offsets slots first s span i idx
  have hk := hWords k (by simp)
  have hLoop := Triple.forRange_const (p := p) (r := 8) (lo := .const 0) (hi := .reg 5)
    (body := buildInjectTablesStep) (P := fun st => st = st₀) (Inv := Inv)
    44 0 k (Nat.zero_le _) hw (fun _ => hk)
    (fun st he => by
      subst st
      refine ⟨Expr.eval_const (Nat.two_pow_pos _),?_,by simp,?_,fun _ _ _ _ => rfl⟩
      · intro j _ hj
        exact Function.update_of_ne hj ..
      · intro j hj
        exact False.elim (Nat.not_lt_zero _ hj))
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq (h.1 5 (by decide) (by decide))) ?_
  swap
  · intro i _ hi st ω ⟨hRegs,hCounter,hAt,hFrame⟩
    let dst := slots+i*span
    let off := first+i*s
    have hM := Nat.mul_le_mul_right span (Nat.le_of_lt hi)
    have hS := Nat.mul_le_mul_right s (Nat.le_of_lt hi)
    have hDW : dst < 2^w := by dsimp [dst]; omega
    have hOw : off < 2^w := by dsimp [off]; omega
    have hMd : i*span < 2^w := by omega
    have hMs : i*s < 2^w := by omega
    have hGW : graphs+i < 2^w := by omega
    have hOt : offsets+i < 2^w := by omega
    have h0 : st.regs 0 = graphs := hRegs 0 (by decide) (by decide)
    have h1 : st.regs 1 = offsets := hRegs 1 (by decide) (by decide)
    have h2 : st.regs 2 = slots := hRegs 2 (by decide) (by decide)
    have h3 : st.regs 3 = first := hRegs 3 (by decide) (by decide)
    have h4 : st.regs 4 = s := hRegs 4 (by decide) (by decide)
    have h6 : st.regs 6 = span := hRegs 6 (by decide) (by decide)
    have h8 : st.regs 7 = idx := hRegs 7 (by decide) (by decide)
    have hIndex : idx+i < 2^w := by omega
    refine runs_start_le ?_
    unfold buildInjectTablesStep
    refine runs_seq_assign_le (v := dst) ?_ ?_
    · have hh : slots+i*span < 2^w := hDW
      simp [Expr.eval,h2,hCounter,h6,hMd,hh,dst]
    refine runs_seq_store_le (x := graphs+i) (v := dst) ?_ (by simp [Expr.eval,Function.update]) ?_
    · simp [Expr.eval,Function.update,h0,hCounter,hGW]
    refine runs_seq_store_le (x := offsets+i) (v := off) ?_ ?_ ?_
    · simp [Expr.eval,Function.update,h1,hCounter,hOt]
    · have hh : first+i*s < 2^w := hOw
      simp [Expr.eval,Function.update,h3,hCounter,h4,hMs,hh,off]
    refine runs_store_le (x := idx+i) (v := i) ?_
      (by simp [Expr.eval,Function.update,hCounter]) ?_ ?_
    · simp [Expr.eval,Function.update,h8,hCounter,hIndex]
    · let updated := Function.update (Function.update (Function.update st.mem (graphs+i) dst)
        (offsets+i) off) (idx+i) i
      refine ⟨⟨?_,by simp,?_,?_⟩,by simp [hCounter]⟩
      · intro j hj h7
        have h9 : j ≠ 9 := by omega
        simpa [Function.update_of_ne h7,Function.update_of_ne h9] using hRegs j hj h7
      · intro j hj
        change updated (graphs+j) = _ ∧ updated (offsets+j) = _ ∧ updated (idx+j) = _
        have keep (a : ℕ) (h1 : a ≠ graphs+i) (h2 : a ≠ offsets+i) (h3 : a ≠ idx+i) :
            updated a = st.mem a := by simp [updated,Function.update_of_ne,h1,h2,h3]
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · obtain ⟨hgl,hol,hil⟩ := hAt j hj
          exact ⟨(keep _ (by omega) (by omega) (by omega)).trans hgl,
            (keep _ (by omega) (by omega) (by omega)).trans hol,
            (keep _ (by omega) (by omega) (by omega)).trans hil⟩
        · have hgO : graphs+j ≠ offsets+j := by omega
          have hgI : graphs+j ≠ idx+j := by omega
          have hoI : offsets+j ≠ idx+j := by omega
          simp only [updated,Function.update_of_ne hgO,Function.update_of_ne hgI,
            Function.update_of_ne hoI,Function.update_self,dst,off,and_self]
      · intro a ha hb hc
        change updated a = mem a
        rw [show updated a = st.mem a by
          simp [updated,Function.update_of_ne,show a ≠ idx+i by omega,
            show a ≠ offsets+i by omega,show a ≠ graphs+i by omega]]
        exact hFrame a (by omega) (by omega) (by omega)
    · simp [Expr.size]
  refine runs_start_le ?_
  unfold buildInjectTablesProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_,_,hAt,hFrame⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _))
    ⟨graphs,offsets,slots,first,s,k,span,idx,rfl,⟨hAt,hFrame⟩,?_,?_,?_⟩ ?_
  · intro i hi
    rw [length_tabList] at hi
    rw [show (tabList k (fun i => slots+i*span))[i] = slots+i*span by simp [tabList]]
    exact (hAt i hi).1
  · intro i hi
    rw [length_tabList] at hi
    rw [show (tabList k (fun i => first+i*s))[i] = first+i*s by simp [tabList]]
    exact (hAt i hi).2.1
  · intro i hi
    rw [List.length_range] at hi
    rw [List.getElem_range]
    exact (hAt i hi).2.2
  · simp [buildInjectTablesContract,Expr.size]
    omega

end MinCostFlow.HierPaths
