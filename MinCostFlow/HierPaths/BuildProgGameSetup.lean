module

public import MinCostFlow.HierPaths.BuildProgChoiceHistory

/-!
# Writing the initial active table and child graphs

Each child starts with an empty graph of the same size. The graph addresses
and the offsets are filled in increasing child order. A zeroed reservation
gives the zero edge count of each graph.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- Initialize the two active entries and the vertex count of one child. -/
def buildGameSetupStep : Stmt :=
  .seq (.assign 8 (.bin .add (.reg 2) (.bin .mul (.reg 7) (.reg 6))))
    (.seq (.store (.bin .add (.reg 0) (.reg 7)) (.reg 8))
      (.seq (.store (.bin .add (.reg 1) (.reg 7))
          (.bin .add (.reg 3) (.bin .mul (.reg 7) (.reg 4))))
        (.store (.reg 8) (.reg 4))))

/-- Args are graph pointers, terminal offsets, first graph slot, first
terminal, child size, number of children, and the size of one slot. -/
def buildGameSetupProc : Stmt :=
  .seq (forRange 7 (.const 0) (.reg 5) buildGameSetupStep) (.ret (.const 0))

theorem buildGameSetupProc_noRand : buildGameSetupProc.NoRand := by
  simp [buildGameSetupProc,buildGameSetupStep,forRange,forUp,Stmt.NoRand]

/-- The written prefixes and the frame outside the three regions. -/
def GameSetupAt (mem after : ℕ → ℕ) (graphs offsets slots first s span n : ℕ) : Prop :=
  (∀ i < n, after (graphs+i) = slots+i*span ∧ after (offsets+i) = first+i*s ∧
    after (slots+i*span) = s) ∧
  ∀ a, (a < graphs ∨ graphs+n ≤ a) → (a < offsets ∨ offsets+n ≤ a) →
    (∀ i < n, a ≠ slots+i*span) → after a = mem a

/-- The setup initializes the graph reservations, with no scan over
their unused cells. -/
def buildGameSetupContract (w : ℕ) : Contract where
  pre args mem := ∃ graphs offsets slots first s k span,
    args = [graphs,offsets,slots,first,s,k,span] ∧
    graphs+k ≤ offsets ∧ offsets+k ≤ slots ∧ 2 ≤ span ∧
    slots+k*span < 2^w ∧ first+k*s < 2^w ∧ 1 < 2^w ∧ ZeroFrom mem graphs
  post args mem _ after := ∃ graphs offsets slots first s k span,
    args = [graphs,offsets,slots,first,s,k,span] ∧
    GameSetupAt mem after graphs offsets slots first s span k ∧
    ListAt after graphs (tabList k (fun i => slots+i*span)) ∧
    ListAt after offsets (tabList k (fun i => first+i*s)) ∧
    (∀ i < k, GraphAt after (slots+i*span) (⟨s,[]⟩ : Graph)) ∧
    ZeroFrom after (slots+k*span)
  cost args _ := 52*(args.getD 5 0)+16

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

private theorem childSlot_separated {i j span : ℕ} (hspan : 2 ≤ span) (hij : i < j) :
    i*span+2 ≤ j*span := by
  have hMul : (i+1)*span ≤ j*span := Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hij)
  rw [Nat.add_mul,Nat.one_mul] at hMul
  omega

/-- Initialization writes exactly three words per child and leaves the
unused part of every reservation zero. -/
theorem buildGameSetupProc_meetsContract {w f : ℕ} {p : Program}
    (hf : p.procs[f]? = some buildGameSetupProc) :
    MeetsContract w p f (buildGameSetupContract w) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨graphs,offsets,slots,first,s,k,span,rfl,hG,hO,hSpan,hWord,hTerm,hw,hZero⟩ := hPre
  let st₀ := startState [graphs,offsets,slots,first,s,k,span] mem pos
  let Inv := fun i (st : State) =>
    (∀ j < 7, st.regs j = st₀.regs j) ∧ st.regs 7 = i ∧
      GameSetupAt mem st.mem graphs offsets slots first s span i
  have hk := hWords k (by simp)
  have hLoop := Triple.forRange_const (p := p) (r := 7) (lo := .const 0) (hi := .reg 5)
    (body := buildGameSetupStep) (P := fun st => st = st₀) (Inv := Inv)
    38 0 k (Nat.zero_le _) hw (fun _ => hk)
    (fun st he => by
      subst st
      refine ⟨Expr.eval_const (Nat.two_pow_pos _),?_,by simp,?_,fun _ _ _ _ => rfl⟩
      · intro j hj
        change Function.update st₀.regs 7 0 j = _
        exact Function.update_of_ne (by omega) ..
      · intro j hj
        exact False.elim (Nat.not_lt_zero _ hj))
    (fun _ _ _ _ h => h.2.1)
    (fun _ _ _ _ h => Expr.eval_reg_of_eq (h.1 5 (by decide))) ?_
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
    have h0 : st.regs 0 = graphs := hRegs 0 (by decide)
    have h1 : st.regs 1 = offsets := hRegs 1 (by decide)
    have h2 : st.regs 2 = slots := hRegs 2 (by decide)
    have h3 : st.regs 3 = first := hRegs 3 (by decide)
    have h4 : st.regs 4 = s := hRegs 4 (by decide)
    have h6 : st.regs 6 = span := hRegs 6 (by decide)
    have hgO : graphs+i < offsets := by omega
    have hoD : offsets+i < dst := (show offsets+i < slots by omega).trans_le (Nat.le_add_right _ _)
    have hgD := hgO.trans_le (Nat.le_trans (Nat.le_add_right offsets i) hoD.le)
    refine runs_start_le ?_
    unfold buildGameSetupStep
    refine runs_seq_assign_le (v := dst) ?_ ?_
    · have hh : slots+i*span < 2^w := hDW
      simp [Expr.eval,h2,hCounter,h6,hMd,hh,dst]
    refine runs_seq_store_le (x := graphs+i) (v := dst) ?_ (by simp [Expr.eval,Function.update]) ?_
    · simp [Expr.eval,Function.update,h0,hCounter,hGW]
    refine runs_seq_store_le (x := offsets+i) (v := off) ?_ ?_ ?_
    · simp [Expr.eval,Function.update,h1,hCounter,hOt]
    · have hh : first+i*s < 2^w := hOw
      simp [Expr.eval,Function.update,h3,hCounter,h4,hMs,hh,off]
    refine runs_store_le (x := dst) (v := s) (by simp [Expr.eval,Function.update])
      (by simp [Expr.eval,Function.update,h4]) ?_ ?_
    · let updated := Function.update (Function.update (Function.update st.mem (graphs+i) dst)
        (offsets+i) off) dst s
      refine ⟨⟨?_,by simp,?_,?_⟩,by simp [hCounter]⟩
      · intro j hj
        have h7 : j ≠ 7 := by omega
        have h8 : j ≠ 8 := by omega
        simpa [Function.update_of_ne h7,Function.update_of_ne h8] using hRegs j hj
      · intro j hj
        change updated (graphs+j) = _ ∧ updated (offsets+j) = _ ∧ updated (slots+j*span) = _
        rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj | rfl
        · have hjG : graphs+j < offsets := by omega
          have hjO : offsets+j < slots := by omega
          have hjS : slots+j*span < dst := by
            have hh := childSlot_separated hSpan hj
            dsimp [dst]
            omega
          obtain ⟨hga,hoa,hsa⟩ := hAt j hj
          dsimp [updated]
          rw [Function.update_of_ne (by omega : graphs+j ≠ dst),
            Function.update_of_ne (by omega : graphs+j ≠ offsets+i),
            Function.update_of_ne (by omega : graphs+j ≠ graphs+i),
            Function.update_of_ne (by omega : offsets+j ≠ dst),
            Function.update_of_ne (by omega : offsets+j ≠ offsets+i),
            Function.update_of_ne (by omega : offsets+j ≠ graphs+i),
            Function.update_of_ne (by omega : slots+j*span ≠ dst),
            Function.update_of_ne (by omega : slots+j*span ≠ offsets+i),
            Function.update_of_ne (by omega : slots+j*span ≠ graphs+i)]
          exact ⟨hga,hoa,hsa⟩
        · simp [updated,Function.update,show graphs+j ≠ dst by omega,
            show offsets+j ≠ dst by omega,show graphs ≠ offsets by omega,dst,off]
      · intro a ha hb hc
        change updated a = mem a
        have hd : a ≠ dst := hc i (Nat.lt_succ_self _)
        dsimp [updated]
        rw [Function.update_of_ne hd,Function.update_of_ne (by omega : a ≠ offsets+i),
          Function.update_of_ne (by omega : a ≠ graphs+i)]
        exact hFrame a (by omega) (by omega) (fun j hj => hc j (hj.trans (Nat.lt_succ_self _)))
    · simp [Expr.size]
  refine runs_start_le ?_
  unfold buildGameSetupProc
  refine runs_seq_triple_le hLoop rfl ?_
  intro st ⟨_,_,hAt,hFrame⟩
  refine runs_ret_le (v := 0) (Expr.eval_const (Nat.two_pow_pos _))
    ⟨graphs,offsets,slots,first,s,k,span,rfl,⟨hAt,hFrame⟩,?_,?_,?_,?_⟩ ?_
  · intro i hi
    rw [length_tabList] at hi
    rw [show (tabList k (fun i => slots+i*span))[i] = slots+i*span by simp [tabList]]
    exact (hAt i hi).1
  · intro i hi
    rw [length_tabList] at hi
    rw [show (tabList k (fun i => first+i*s))[i] = first+i*s by simp [tabList]]
    exact (hAt i hi).2.1
  · intro i hi
    change ListAt st.mem (slots + i*span) [s,0]
    intro j hj
    have hCases : j = 0 ∨ j = 1 := by simp at hj; omega
    rcases hCases with rfl | rfl
    · exact (hAt i hi).2.2
    · have hh := Nat.le_add_right slots (i*span)
      rw [hFrame _ (Or.inr (by omega)) (Or.inr (by omega)) (fun j hj => ?_)]
      · exact hZero _ (by omega)
      · by_cases hji : j ≤ i
        · have hh' := Nat.mul_le_mul_right span hji
          omega
        · have hh' := childSlot_separated hSpan (show i < j by omega)
          omega
  · intro a ha
    have hl : slots ≤ a := (Nat.le_add_right _ _).trans ha
    rw [hFrame _ (Or.inr (by omega)) (Or.inr (by omega)) (fun j hj => ?_)]
    · exact hZero a (by omega)
    · have hh := childSlot_separated hSpan hj
      omega
  · simp [buildGameSetupContract,Expr.size]
    omega

end MinCostFlow.HierPaths
