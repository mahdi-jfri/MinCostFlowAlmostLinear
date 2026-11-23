module

public import MinCostFlow.HierPaths.BuildProgCoreCall
public import MinCostFlow.HierPaths.BuildProgPlayerViews
public import MinCostFlow.HierPaths.BuildProgRequest

/-!
# Preparing an active child in a game round

The core reads the current game graph. An expander reply retains the certified
set and needs no request. A cut reply is followed by a mask and its two packed
request sides.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- Args are `[q, g, M, r, h, off]`. Return the end of the prepared child block. -/
def buildPrepareChildProc (fCore fRequest : ℕ) : Stmt :=
  .seq (.assign 12 (.reg 5)) (.seq (buildCoreCall fCore)
    (.seq (.cond (.reg 6) .nop
      (.seq (.assign 7 (.load (.reg 1)))
        (.seq (.assign 8 (.bin .add (.reg 5) (.reg 7)))
          (.seq (.call 9 fRequest [
              .bin .add (.reg 4) (.const 4),
              .bin .sub (.load (.bin .add (.reg 4) (.const 2))) (.const 1),
              .reg 7, .reg 5, .reg 8, .reg 12])
            (.assign 5 (.bin .add (.bin .add (.reg 8) (.reg 7)) (.reg 7)))))))
      (.ret (.reg 5))))

/-- The prepared block keeps the core reply at `h`. Under the bump contract, the core
returns a cursor `e ≥ h + (coreResultWords answer).length`. An expander stops at `v = e`.
A cut writes a mask of size `s` at `e` and the two packed request sides at `e + s`,
ending at `v = e + 3 * s` (so `e + s = v - 2 * s`). -/
def PreparedChildAt (mem : ℕ → ℕ) (h v s off : ℕ) (answer : CoreResult) : Prop :=
  ListAt mem h (coreResultWords answer) ∧
  match answer with
  | .expander _ => h + (coreResultWords answer).length ≤ v
  | .cut U =>
    ∃ e, h + (coreResultWords (.cut U)).length ≤ e ∧ v = e + 3 * s ∧
      ListAt mem (e + s) ((requestSides s off U).1 ++ (requestSides s off U).2)

/-- Minimum (compact) end of the prepared block when the core has zero bump gap. -/
def preparedChildEnd (h s : ℕ) (answer : CoreResult) : ℕ :=
  let e := h + (coreResultWords answer).length
  match answer with
  | .expander _ => e
  | .cut _ => e + 3 * s

/-- The caller provides room above the core reply for one mask and two output arrays
of the child size. Memory below the heap remains available for the next child. -/
def buildPrepareChildContract (w K M r q : ℕ)
    (core : ℕ → Graph → CoreResult) (coreCost : ℕ → Graph → ℕ) (sC : ℕ → ℕ) (G : Graph) :
    Contract where
  pre args mem := ∃ g h off, args = [q, g, M, r, h, off] ∧
    (CoreExactProcContract w K M r core coreCost sC q G).pre [q, g, M, r, h] mem ∧
    2 ≤ G.n ∧ off + G.n < 2 ^ w ∧ h + sC G.encode.length + 3 * G.n < 2 ^ w
  post args mem v mem' := ∃ g h off, args = [q, g, M, r, h, off] ∧
    h ≤ v ∧ v ≤ h + sC G.encode.length + 3 * G.n ∧
    (∀ j < h, mem' j = mem j) ∧ ZeroFrom mem' v ∧
    v = preparedChildEnd h G.n (core q G) ∧
    PreparedChildAt mem' h v G.n off (core q G)
  cost _ _ := K * (coreCost q G + G.encode.length + 1) + 160 * G.n + 250

theorem buildPrepareChildProc_noRand (fCore fRequest : ℕ) :
    (buildPrepareChildProc fCore fRequest).NoRand := by
  simp [buildPrepareChildProc, buildCoreCall, Stmt.NoRand]

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner MinCostFlow.ExpanderDecomp

/-- The prepared block end is at least the compact minimum end. -/
theorem PreparedChildAt.le_end {mem : ℕ → ℕ} {h v s off : ℕ} {answer : CoreResult}
    (hAt : PreparedChildAt mem h v s off answer) : preparedChildEnd h s answer ≤ v := by
  cases answer with
  | expander _ => exact hAt.2
  | cut _ =>
    obtain ⟨_, e, he, hv, _⟩ := hAt
    simp only [preparedChildEnd]
    omega

/-- The prepared block end is at least the end of the core result words. -/
theorem PreparedChildAt.core_end_le {mem : ℕ → ℕ} {h v s off : ℕ} {answer : CoreResult}
    (hAt : PreparedChildAt mem h v s off answer) : h + (coreResultWords answer).length ≤ v := by
  have h1 := hAt.le_end
  cases answer <;> simp only [preparedChildEnd] at h1 <;> omega

/-- A later heap allocation preserves an earlier prepared child block. -/
theorem PreparedChildAt.frame {mem mem' : ℕ → ℕ} {h v s off : ℕ} {answer : CoreResult}
    (hAt : PreparedChildAt mem h v s off answer) (hFrame : ∀ j, h ≤ j → j < v → mem' j = mem j)
    (hCutSub : ∀ U, answer = .cut U → U ⊆ Finset.range s) :
    PreparedChildAt mem' h v s off answer := by
  cases answer with
  | expander S =>
    obtain ⟨hCore, hEnd⟩ := hAt
    refine ⟨WordRAM.ListAt.congr hCore (fun j hj₀ hj => hFrame j hj₀ (hj.trans_le hEnd)), hEnd⟩
  | cut U =>
    obtain ⟨hCore, e, he, hv, hCut⟩ := hAt
    have hLen : ((requestSides s off U).1 ++ (requestSides s off U).2).length ≤ s := by
      have hA : (bisectOf s U).card + (Finset.range s \ bisectOf s U).card ≤ s := by
        have hSub : bisectOf s U ⊆ Finset.range s := by
          exact padHalf_subset (smallerSide_subset (hCutSub U rfl))
        rw [Finset.card_sdiff_of_subset hSub, Finset.card_range]
        have hCard := Finset.card_le_card hSub
        rw [Finset.card_range] at hCard
        omega
      simpa [requestSides, finsetWords, card_shiftSet] using hA
    refine ⟨WordRAM.ListAt.congr hCore (fun j hj₀ hj => hFrame j (by omega) (by omega)),
      e, he, hv, ?_⟩
    exact WordRAM.ListAt.congr hCut (fun j hj₀ hj => hFrame j (by omega) (by omega))

/-- Preparing an active child performs the core action of the child game (`lemma_3`) before the
batched routing call. -/
theorem buildPrepareChildProc_meetsContract {w K M r q : ℕ}
    {core : ℕ → Graph → CoreResult} {coreCost : ℕ → Graph → ℕ} {sC : ℕ → ℕ}
    {G : Graph} {p : Program} {f fCore fRequest fMask fPad fPack : ℕ}
    (hf : p.procs[f]? = some (buildPrepareChildProc fCore fRequest))
    (hCore : ProvidesExactCore w K M r core coreCost sC p fCore)
    {cfg : ParamConfig} (hPlayer : IsCorePlayer cfg M r core coreCost)
    (hReq : p.procs[fRequest]? = some (buildRequestProc fMask fPad fPack))
    (hMask : p.procs[fMask]? = some buildCutMaskProc)
    (hPad : p.procs[fPad]? = some buildPadHalfProc)
    (hPack : p.procs[fPack]? = some buildCutPackProc) :
    MeetsContract w p f (buildPrepareChildContract w K M r q core coreCost sC G) := by
  refine meetsContract_of_runs hf fun args mem pos ω hWords hPre => ?_
  obtain ⟨g, h, off, rfl, hPre, hs, ho, hRoom⟩ := hPre
  have hCallPre := hPre
  obtain ⟨⟨_, _, hEq, hg, hgEnd, hq, hValid, hLoop, hn, hDeg⟩, _, _⟩ := hPre
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl, rfl⟩ := hEq
  have hSpec := hPlayer.spec q G hq hValid hLoop hn hDeg
  have hArgs : ∀ i ∈ [q, g, M, r, h], i < 2 ^ w := by
    intro i hi
    apply hWords
    simpa [List.mem_cons, or_assoc] using
      (show i ∈ [q, g, M, r, h] ∨ i = off from Or.inl hi)
  refine runs_start_le ?_
  unfold buildPrepareChildProc
  refine runs_seq_assign_le (v := off) (Expr.eval_reg_of_eq (by rfl)) ?_
  refine runs_seq_triple_le (buildCoreCall_triple (saved := off) hCore hCallPre hArgs)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, by simp⟩ ?_
  intro st ⟨hTag, h0, h1, h2, h3, h4, hSaved, hCorePost⟩
  obtain ⟨⟨hLo, hHi, hBelow, hZero, _⟩, _, _, hEq, hAt, hv⟩ := hCorePost
  simp only [List.cons.injEq, and_true, true_and] at hEq
  obtain ⟨rfl, rfl⟩ := hEq
  let e := st.regs 5
  change h ≤ e at hLo
  change e ≤ h + sC G.encode.length at hHi
  change ∀ j < h, st.mem j = mem j at hBelow
  change ZeroFrom st.mem e at hZero
  change e = h + (coreResultWords (core q G)).length at hv
  have heFit : e + 3 * G.n < 2 ^ w := by omega
  have hOffReg : st.regs 5 = e := rfl
  refine runs_seq_cond_le (Expr.eval_reg_of_eq hTag) ?_ ?_
  · intro hNonzero
    cases hRes : core q G with
    | cut U => exact False.elim (hNonzero (by simp [hRes, coreTag]))
    | expander S =>
      refine runs_seq_nop_le ?_
      refine runs_ret_le (Expr.eval_reg_of_eq hOffReg) ?_ ?_
      · simp only [Outcome.value]
        exact ⟨g, h, off, rfl, hLo, by omega, hBelow, hZero,
          by simpa [hRes, preparedChildEnd] using hv, hAt, by simpa [hRes] using hv.symm.le⟩
      · simp [buildPrepareChildContract, Expr.size]; omega
  · intro hZeroTag
    cases hRes : core q G with
    | expander S => simp [hRes, coreTag] at hZeroTag
    | cut U =>
      rw [hRes] at hSpec hAt hv
      have hU : U ⊆ Finset.range G.n := hSpec.1
      have hnRead : st.mem g = G.n := (hBelow g (by
        have hLen : 0 < G.encode.length := by simp [Graph.encode]
        omega)).trans (hg 0 (by simp [Graph.encode]))
      obtain ⟨hSet, hLenWord⟩ := coreSet_view hAt
      have hSetEnd : h + 4 + U.card ≤ e := by
        rw [hv]
        simp [coreResultWords, layoutList, csrList, csrOffsets, csrData, List.range_succ, finsetWords]
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
        refine ⟨g, h, off, rfl, by omega, by omega, ?_, ?_, ?_, ?_⟩
        · intro j hj
          exact (hFrame j (Or.inl (by omega)) (Or.inl (by omega))).trans (hBelow j hj)
        · intro j hj
          exact (hFrame j (Or.inr (by omega)) (Or.inr (by omega))).trans (hZero j (by omega))
        · simp only [preparedChildEnd, hRes]; omega
        · simp only [PreparedChildAt.eq_def, hRes]
          refine ⟨?_, e, by omega, rfl, hRequest⟩
          exact WordRAM.ListAt.congr hAt (fun j _ hj => hFrame j (Or.inl (by omega)) (Or.inl (by omega)))
      · simp [buildPrepareChildContract, buildRequestContract, argsSize, Expr.size]
        omega

end MinCostFlow.HierPaths
