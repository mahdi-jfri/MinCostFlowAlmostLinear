module

public import MinCostFlow.HierPaths.BuildProgPrepareChild
import MinCostFlow.HierPaths.BuildProgCoreChoice

/-!
# Preparing an arbitrary certified reply

The prepared block contains the core's actual answer. A cut also leaves
the two padded sides in terminal order.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Prepare the certified result returned by the core. There may be several valid
results for the same graph, and the output records the one from this call. -/
def buildPrepareChoiceContract (w K M r q : ℕ) (coreCost : ℕ → Graph → ℕ)
    (sC : ℕ → ℕ) (G : Graph) : Contract where
  pre args mem := ∃ g h off, args = [q,g,M,r,h,off] ∧
    (CoreProcContract w K M r coreCost sC q G).pre [q,g,M,r,h] mem ∧
    2 ≤ G.n ∧ off + G.n < 2^w ∧ h + sC G.encode.length + 3*G.n < 2^w
  post args mem v mem' := ∃ g h off, args = [q,g,M,r,h,off] ∧
    h ≤ v ∧ v ≤ h + sC G.encode.length + 3*G.n ∧
    (∀ a<h, mem' a = mem a) ∧ ZeroFrom mem' v ∧
    ∃ res, CoreOutcomeSpec ParamConfig.default M q G res ∧ PreparedChildAt mem' h v G.n off res
  cost _ _ := K * (coreCost q G + G.encode.length + 1) + 160 * G.n + 256

/-- Preparing an active child performs the core action of the child game (`lemma_3`) before the
batched routing call. -/
theorem buildPrepareChoiceProc_meetsContract {w K M r q : ℕ}
    {coreCost : ℕ → Graph → ℕ} {sC : ℕ → ℕ}
    {G : Graph} {p : Program} {f fCore fRequest fMask fPad fPack : ℕ}
    (hf : p.procs[f]? = some (buildPrepareChildProc fCore fRequest))
    (hCore : ProvidesCore w K M r coreCost sC p fCore)
    (hReq : p.procs[fRequest]? = some (buildRequestProc fMask fPad fPack))
    (hMask : p.procs[fMask]? = some buildCutMaskProc)
    (hPad : p.procs[fPad]? = some buildPadHalfProc)
    (hPack : p.procs[fPack]? = some buildCutPackProc) :
    MeetsContract w p f (buildPrepareChoiceContract w K M r q coreCost sC G) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨g, h, off, rfl, hPre, hs, ho, hRoom⟩ := hPre
  have hCallPre := hPre
  obtain ⟨⟨_, _, hEq, hg, hgEnd, hq, hrl, hValid, hLoop, hn, hDeg⟩, _, _⟩ := hPre
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl, rfl⟩ := hEq
  have hArgs : ∀ i ∈ [q, g, M, r, h], i < 2 ^ w := by
    intro i hi
    apply hWords
    simpa [List.mem_cons, or_assoc] using
      (show i ∈ [q, g, M, r, h] ∨ i = off from Or.inl hi)
  refine runs_start_le ?_
  unfold buildPrepareChildProc
  refine runs_seq_assign_le (v := off) (Expr.eval_reg_of_eq (by rfl)) ?_
  refine runs_seq_triple_le (buildCoreChoice_triple (saved := off) hCore hCallPre hArgs)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩ ?_
  intro st ⟨h0,h1,h2,h3,h4,hSaved,hLo,hHi,hBelow,hZero,res,hSpec,hAt,hv,hTag⟩
  let e := st.regs 5
  change h ≤ e at hLo
  change e ≤ h + sC G.encode.length at hHi
  change ∀ j < h, st.mem j = mem j at hBelow
  change ZeroFrom st.mem e at hZero
  change h + (coreResultWords res).length ≤ e at hv
  have heFit : e + 3 * G.n < 2 ^ w := by omega
  have hOffReg : st.regs 5 = e := rfl
  refine runs_seq_cond_le (Expr.eval_reg_of_eq hTag) ?_ ?_
  · intro hNonzero
    cases hRes : res with
    | cut U => exact False.elim (hNonzero (by simp [hRes, coreTag]))
    | expander S =>
      refine runs_seq_nop_le ?_
      refine runs_ret_le (Expr.eval_reg_of_eq hOffReg) ?_ ?_
      · simp only [Outcome.value]
        exact ⟨g, h, off, rfl, hLo, by omega, hBelow, hZero, res, hSpec, hAt, by simpa [hRes] using hv⟩
      · simp [buildPrepareChoiceContract, Expr.size]; omega
  · intro hZeroTag
    cases hRes : res with
    | expander S => simp [hRes, coreTag] at hZeroTag
    | cut U =>
      rw [hRes] at hSpec hAt hv
      have hU : U ⊆ Finset.range G.n := hSpec.1
      have hnRead : st.mem g = G.n := (hBelow g (by
        have hLen : 0 < G.encode.length := by simp [Graph.encode]
        omega)).trans (hg 0 (by simp [Graph.encode]))
      obtain ⟨hSet, hLenWord⟩ := coreSet_view hAt
      have hSetEnd : h + 4 + U.card ≤ e := by
        have hCLen : (coreResultWords (.cut U)).length = 4 + U.card := by
          simp [coreResultWords, layoutList, csrList, csrOffsets, csrData, List.range_succ, finsetWords]
          omega
        omega
      have h4w : 4 < 2 ^ w := by omega
      have h2w : 2 < 2 ^ w := by omega
      have h1w : 1 < 2 ^ w := by omega
      have hh4 : h + 4 < 2 ^ w := by omega
      have hh2 : h + 2 < 2 ^ w := by omega
      have hUw : U.card < 2 ^ w := by omega
      have heS : e + G.n < 2 ^ w := by omega
      have hoff : off < 2 ^ w := by omega
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := G.n) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq h1) hnRead) ?_
      refine runs_seq_assoc_le ?_
      refine runs_seq_assign_le (v := e + G.n) ?_ ?_
      · simp [Expr.eval, Function.update, hOffReg, heS]
      refine runs_seq_assoc_le ?_
      refine runs_seq_call_le (buildRequestProc_meetsContract hReq hMask hPad hPack)
        (vs := [h + 4, U.card, G.n, e, e + G.n, off]) ?_ ?_
        ⟨h + 4, e, e + G.n, off, rfl, hSet, hU, hs, hSetEnd, le_rfl, by omega, ho⟩ ?_
      · simp [evalArgs, Expr.eval, Function.update, h4, h4w, hh4, h2w, hh2,
          h1w, hLenWord, hUw, hOffReg, hSaved]
      · wram_words
      intro _ mem' pos' hPost
      obtain ⟨_, _, _, _, hEq, _, hRequest, hFrame⟩ := hPost
      simp only [List.cons.injEq, and_true, true_and] at hEq
      obtain ⟨rfl, rfl, rfl, rfl⟩ := hEq
      have hTwo : e + G.n + G.n < 2 ^ w := by omega
      have hThree : e + G.n + G.n + G.n = e + 3 * G.n := by omega
      refine runs_seq_assign_le (v := e + 3 * G.n) ?_ ?_
      · simp [Expr.eval, Function.update, hTwo, hThree, heFit]
      refine runs_ret_le (v := e + 3 * G.n) (Expr.eval_reg_of_eq (by simp)) ?_ ?_
      · simp only [Outcome.value]
        refine ⟨g, h, off, rfl, by omega, by omega, ?_, ?_, ?_⟩
        · intro j hj
          exact (hFrame j (Or.inl (by omega)) (Or.inl (by omega))).trans (hBelow j hj)
        · intro j hj
          exact (hFrame j (Or.inr (by omega)) (Or.inr (by omega))).trans (hZero j (by omega))
        · refine ⟨.cut U,hSpec,?_⟩
          simp only [PreparedChildAt.eq_def]
          refine ⟨?_, e, hv, rfl, hRequest⟩
          exact WordRAM.ListAt.congr hAt (fun j _ hj => hFrame j (Or.inl (by omega)) (Or.inl (by omega)))
      · simp [buildPrepareChoiceContract, buildRequestContract, argsSize, Expr.size]
        omega

end MinCostFlow.HierPaths
