module

public import MinCostFlow.HierPaths.InitSections

/-!
# A short section word by word

The header of the block is 15 words, each computed by its own small procedure. `writeVals fs i`
calls each `f ∈ fs` with the arguments `r0, …, r6`, stores the result at `r6 + i + j`, and at
the end returns `r6 + i + |fs|`. Each `f` meets `ValContract`: it returns `val base` and leaves
memory unchanged. `writeVals_runs` says what memory it leaves, and `valsWriter_meetsContract`
turns it into `SecContract` for the section `[val₀ base, val₁ base, …]`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- A procedure computing one word: procedure number, value and cost. -/
structure ValProc where
  f : ℕ
  val : List ℕ → ℕ
  cost : ℕ

/-- The contract of a word procedure: with the six arguments `base` meeting `Inv` (and a
seventh argument), it returns `val base` and leaves memory unchanged. -/
def ValContract (Inv : List ℕ → (ℕ → ℕ) → Prop) (q : ValProc) : Contract where
  pre args mem := ∃ base c, args = base ++ [c] ∧ base.length = 6 ∧ Inv base mem
  post args mem v mem' := ∃ base c, args = base ++ [c] ∧ v = q.val base ∧ mem' = mem
  cost _ _ := q.cost

/-- Call each word procedure, store its result at `r6 + i + j`; return the end. -/
def writeVals : List ValProc → ℕ → Stmt
  | [], i => .ret (.bin .add (.reg 6) (.const i))
  | q :: qs, i => .seq (.call 7 q.f secArgs)
      (.seq (.store (.bin .add (.reg 6) (.const i)) (.reg 7)) (writeVals qs (i + 1)))

/-- **What `writeVals` leaves.** -/
theorem writeVals_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {Inv : List ℕ → (ℕ → ℕ) → Prop}
    (hInv : ∀ base mem mem', Inv base mem → (∀ y < base.getD 5 0, mem' y = mem y) →
      Inv base mem')
    (base : List ℕ) (hbase : base.length = 6) (hbw : ∀ v ∈ base, v < 2 ^ w) :
    ∀ (qs : List ValProc) (i : ℕ) (st : State) (k T : ℕ),
      (∀ q ∈ qs, MeetsContract w p q.f (ValContract Inv q)) →
      regs6 st = base → Inv base st.mem → base.getD 5 0 ≤ st.regs 6 →
      st.regs 6 + i + qs.length < 2 ^ w →
      k + ((qs.map fun q => q.cost + 20).sum + 5) ≤ T →
      ∃ o st' c, Runs w p ω (writeVals qs i) st o st' c ∧
        (o = .returned (st.regs 6 + i + qs.length) ∧
          (∀ j (hj : j < qs.length), st'.mem (st.regs 6 + i + j) = qs[j].val base) ∧
          (∀ y, (y < st.regs 6 + i ∨ st.regs 6 + i + qs.length ≤ y) → st'.mem y = st.mem y)) ∧
        k + c ≤ T := by
  intro qs
  induction qs with
  | nil =>
    intro i st k T _ _ _ _ hb hT
    have hi : i < 2 ^ w := by simp at hb; omega
    unfold writeVals
    refine runs_ret_le (v := st.regs 6 + i)
      (Expr.eval_add (Expr.eval_reg_of_eq rfl) (Expr.eval_const hi) (by simpa using hb))
      ⟨by simp, fun j hj => by simp at hj, fun _ _ => rfl⟩ ?_
    simp [Expr.size] at hT ⊢
    omega
  | cons q qs ih =>
    intro i st k T hf hr hI hc hb hT
    set c₀ := st.regs 6 with hc₀
    have hci : c₀ + i < 2 ^ w := by simp at hb; omega
    have hi : i < 2 ^ w := by omega
    have hwords : ∀ v ∈ base ++ [c₀], v < 2 ^ w := by
      intro v hv
      rcases List.mem_append.mp hv with hv | hv
      · exact hbw v hv
      · simp at hv; omega
    have hargs : evalArgs w st secArgs = some (base ++ [c₀]) := by
      rw [evalArgs_secArgs, hr]
    unfold writeVals
    refine runs_seq_call_le (hf q (by simp)) hargs hwords ⟨base, c₀, rfl, hbase, hI⟩ ?_
    intro v mem₂ pos₂ hpost
    obtain ⟨base', c', hargs', hv, hmem⟩ := hpost
    have hbb : base = base' := by
      have hl : base'.length = base.length := by
        have := congrArg List.length hargs'
        simp at this; omega
      exact (List.append_inj hargs'.symm hl).1.symm
    subst hbb hmem
    refine runs_seq_store_le (x := c₀ + i) (v := v)
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update, hc₀]))
        (Expr.eval_const hi) hci) (Expr.eval_reg_of_eq (by simp)) ?_
    let st₂ : State := ⟨Function.update st.mem (c₀ + i) v, Function.update st.regs 7 v, pos₂⟩
    have hr₂ : regs6 st₂ = base := by
      rw [← hr]; simp [regs6, st₂, Function.update]
    have h6₂ : st₂.regs 6 = c₀ := by simp [st₂, hc₀]
    have hI₂ : Inv base st₂.mem := hInv base st.mem _ hI fun y hy => by
      simp only [st₂]
      rw [Function.update_of_ne (by omega)]
    have hcostIH : (k + argsSize secArgs + (ValContract Inv q).cost (base ++ [c₀]) st.mem + 2 +
        (Expr.bin .add (.reg 6) (.const i)).size + (Expr.reg 7).size + 2) +
        ((qs.map fun q => q.cost + 20).sum + 5) ≤ T := by
      simp only [List.map_cons, List.sum_cons] at hT
      simp only [ValContract, secArgs, argsSize, Expr.size]
      omega
    obtain ⟨o, st', c, hrun, ⟨ho, hval, hfr⟩, hcost⟩ :=
      ih (i + 1) st₂ _ T (fun q' hq' => hf q' (by simp [hq'])) hr₂ hI₂ (by rw [h6₂]; omega)
        (by rw [h6₂]; simp at hb; omega) hcostIH
    rw [h6₂] at ho hval hfr
    refine ⟨o, st', c, hrun, ⟨?_, ?_, ?_⟩, hcost⟩
    · rw [ho]; simp; omega
    · intro j hj
      rcases j with _ | j
      · rw [Nat.add_zero, hfr (c₀ + i) (Or.inl (by omega))]
        simp [st₂, hv]
      · rw [show c₀ + i + (j + 1) = c₀ + (i + 1) + j by omega, hval j (by simpa using hj)]
        simp
    · intro y hy
      simp only [List.length_cons] at hy
      rw [hfr y (by omega)]
      simp only [st₂]
      rw [Function.update_of_ne (by omega)]

/-- The writer of a section of words as a `SecProc`. -/
def valsSec (qs : List ValProc) (f : ℕ) : SecProc where
  f := f
  l base := qs.map fun q => q.val base
  cost _ := (qs.map fun q => q.cost + 20).sum + 5

/-- **A section of words by `writeVals` meets `SecContract`**, when each word procedure meets
`ValContract` and `Inv` depends only on memory below `base[5]`. -/
theorem valsWriter_meetsContract {w : ℕ} {p : Program} {f : ℕ}
    {Inv : List ℕ → (ℕ → ℕ) → Prop}
    (hInv : ∀ base mem mem', Inv base mem → (∀ y < base.getD 5 0, mem' y = mem y) →
      Inv base mem')
    {qs : List ValProc} (hf : ∀ q ∈ qs, MeetsContract w p q.f (ValContract Inv q))
    (hp : p.procs[f]? = some (writeVals qs 0)) :
    MeetsContract w p f (SecContract w Inv (valsSec qs f)) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, c, rfl, hbase, hI, hz, hc, hcw⟩ := hpre
  simp only [valsSec, List.length_map] at hcw
  have hbw : ∀ v ∈ base, v < 2 ^ w := fun v hv => hw v (List.mem_append_left _ hv)
  have hr : regs6 (startState (base ++ [c]) mem pos) = base := by
    match base, hbase with
    | [a0, a1, a2, a3, a4, a5], _ => rfl
  have h6 : (startState (base ++ [c]) mem pos).regs 6 = c := by
    match base, hbase with
    | [a0, a1, a2, a3, a4, a5], _ => rfl
  have hT : 0 + ((qs.map fun q => q.cost + 20).sum + 5) ≤
      (SecContract w Inv (valsSec qs f)).cost (base ++ [c]) mem := by
    simp [SecContract, valsSec]
  obtain ⟨o, st', c', hrun, ⟨ho, hval, hfr⟩, hcost⟩ :=
    writeVals_runs (ω := ω) hInv base hbase hbw qs 0 _ 0 _ hf hr hI (by rw [h6]; omega)
      (by rw [h6]; omega) hT
  rw [h6] at ho hval hfr
  refine ⟨o, st', c', hrun, ⟨base, c, rfl, ?_, ?_, ?_, ?_⟩, by omega⟩
  · rw [ho]; simp only [Outcome.value, valsSec, List.length_map]; omega
  · intro j hj
    simp only [valsSec, List.length_map] at hj
    have := hval j hj
    simp only [Nat.add_zero] at this
    simp [valsSec, this]
  · intro y hy
    rw [ho] at hy
    simp only [Outcome.value, valsSec, List.length_map] at hy
    rw [hfr y (Or.inr (by omega))]
    exact hz y (by omega)
  · intro y hy
    exact hfr y (Or.inl (by omega))

end MinCostFlow.HierPaths
