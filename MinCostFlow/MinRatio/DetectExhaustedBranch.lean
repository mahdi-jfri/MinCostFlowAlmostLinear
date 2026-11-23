module

public import MinCostFlow.MinRatio.DetectReserved
public import MinCostFlow.MinRatio.DetectForestAccounts
import WordRAM.Tactic

/-!
# The exhausted branch of Detect

The proof of Theorem 5.1 (pages 29–30) stops reporting when no
nonnegative residual remains. The report cursor gives the number
of names written. The finalizer writes that count and returns the
actual heap left by the last search.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain LinkCut IPM.Machine

/-- Register 17 holds the report header, register 8 the next report
cell, and register 2 the heap from the exhausted search. -/
@[expose] def detectExhaustedBranch (finish : ℕ) : Stmt :=
  .call 18 finish [.reg 17,
    .bin .sub (.reg 8) (.bin .add (.reg 17) (.const 1)), .reg 2] ;;
  .ret (.reg 18)

/-- The final branch has no random statements. -/
theorem detectExhaustedBranch_noRand (finish : ℕ) : (detectExhaustedBranch finish).NoRand := by
  simp [detectExhaustedBranch, Stmt.NoRand]

/-- Exhaustion finalizes the header without truncating the active heap. -/
theorem detectExhaustedBranch_runs {w finish base heap : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} (reported : List ℕ)
    (hf : MeetsContract w p finish (detectFinishKeepHeapContract w heap reported))
    (hbase : st.regs 17 = base) (hcursor : st.regs 8 = base + 1 + reported.length)
    (hheap : st.regs 2 = heap)
    (hpre : (detectFinishReservedContract w heap reported).pre [base, reported.length] st.mem) :
    ∃ out cost,
      Runs w p ω (detectExhaustedBranch finish) st (.returned heap) out cost ∧
      (detectFinishKeepHeapContract w heap reported).post
        [base, reported.length, heap] st.mem heap out.mem ∧ cost ≤ 27 := by
  have hh : heap < 2 ^ w := by
    obtain ⟨a, _, _, hw, _, _, _⟩ := hpre
    exact hw
  have hb : base + 1 + reported.length ≤ heap := by
    obtain ⟨a, heq, hle, _, _, _, _⟩ := hpre
    have ha : base = a := (List.cons.inj heq).1
    rwa [ha]
  have hb' : base < 2 ^ w := by omega
  have hl : reported.length < 2 ^ w := by omega
  have hone : 1 < 2 ^ w := by omega
  have hbaseEnd : base + 1 < 2 ^ w := by omega
  have hcount : base + 1 + reported.length - (base + 1) = reported.length := by omega
  have hargs : evalArgs w st [.reg 17, .bin .sub (.reg 8) (.bin .add (.reg 17) (.const 1)), .reg 2] =
      some [base, reported.length, heap] := by
    simp [evalArgs, Expr.eval, hbase, hcursor, hheap, hone, hbaseEnd, hcount, hl]
  have hr : ∃ o out c,
      Runs w p ω (detectExhaustedBranch finish) st o out c ∧
      (o = .returned heap ∧
        (detectFinishKeepHeapContract w heap reported).post
          [base, reported.length, heap] st.mem heap out.mem) ∧ c ≤ 27 := by
    apply runs_start_le
    unfold detectExhaustedBranch
    refine runs_seq_call_le hf (vs := [base, reported.length, heap]) hargs
      (by wram_words) ⟨base, rfl, hpre⟩ ?_
    intro ret out pos hpost
    have hr := hpost.1
    subst ret
    refine runs_ret_le (v := heap) (by eval_expr) ⟨rfl, hpost⟩ ?_
    simp [detectFinishKeepHeapContract, argsSize, Expr.size]
  obtain ⟨_, out, cost, hrun, ⟨rfl, hpost⟩, hc⟩ := hr
  exact ⟨out, cost, hrun, hpost, hc⟩

/-- An exhausted search finalizes the IPM report and leaves the
evaluated forest representing the post-Detect model accounts. -/
theorem detectExhaustedBranch_model_runs {w finish base heap handle m : ℕ}
    (F : MinRatioFormat w) (cfg : Alg2Config) {G : MGraph} {κ α : ℝ}
    {rate : ℕ → ℕ} {allocation : ℕ → List ℕ → ℕ}
    {model : (algorithm2_dsWithFailureWith cfg κ).State}
    {p : Program} {st : State} {ω : ℕ → Bool}
    {tree : PathTreeState} {trees : List AuxTree} {free : List ℕ} {depth slotOf : ℕ → ℕ}
    (reported : List ℕ)
    (hf : MeetsContract w p finish (detectFinishKeepHeapContract w heap reported))
    (hbase : st.regs 17 = base) (hcursor : st.regs 8 = base + 1 + reported.length)
    (hheap : st.regs 2 = heap)
    (hpre : (detectFinishReservedContract w heap reported).pre [base, reported.length] st.mem)
    (hfit : MinRatioStateFits (algorithm2_dsWithFailureWith cfg κ) G F.fmt.limbBits F.limbs
      F.fmt.precision model)
    (hi : LctInvWith pathPayload tree trees free depth)
    (ha : DetectForestAccounts model F.fmt.precision slotOf reported.toFinset tree trees)
    (hedge : ∀ e ∈ model.extG.E, isEdgeSlot tree.n (slotOf e))
    (heps : 0 < cfg.ε) (hl : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hsub : reported.toFinset ⊆ (algorithm2_detect cfg model).1)
    (hstop : ¬ ∃ slot, pathTreeReady tree slot) :
    ∃ out cost,
      Runs w p ω (detectExhaustedBranch finish) st (.returned heap) out cost ∧
      (minRatioMachineContract F (algorithm2_dsWithFailureWith cfg κ) G m κ α rate allocation).post
        2 model [handle, base] st.mem (algorithm2_detect cfg model).2 out.mem ∧
      DetectForestAccounts (algorithm2_detect cfg model).2 F.fmt.precision slotOf ∅ tree trees ∧
      (detectFinishKeepHeapContract w heap reported).post
        [base, reported.length, heap] st.mem heap out.mem ∧ cost ≤ 27 := by
  obtain ⟨out, cost, hrun, hpost, hcost⟩ :=
    detectExhaustedBranch_runs (ω := ω) reported hf hbase hcursor hheap hpre
  have hbelow := detectForestAccounts_below_threshold model hi ha hedge heps hl
    (fun slot hready => hstop ⟨slot, hready⟩)
  obtain ⟨_, hmodel, hreset⟩ :=
    detectFinishKeepHeap_of_exhausted F cfg hfit heps hsub hbelow hpost
      (m := m) (κ := κ) (α := α) (rate := rate) (allocation := allocation) (handle := handle)
  exact ⟨out, cost, hrun, hmodel, detectForestAccounts_next model ha hreset, hpost, hcost⟩

end MinCostFlow.MinRatio
