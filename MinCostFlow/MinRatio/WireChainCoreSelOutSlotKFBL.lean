module

public import MinCostFlow.MinRatio.WireChainCoreSelOutCopyKFBL
public import MinCostFlow.MinRatio.WireChainCoreSelectOutKFBL
import WordRAM.Tactic

/-!
# One select-output slot of the chain-update core (`WireChainCoreSelOutSlotKFBL`)

At each level that `Update` does not rebuild, the chain-update core must leave a 12-word slot that
the select part of `Update` reads (`UpdateCoreSelectOutAt`, `WireChainCoreSpecKFBL.lean`). The
sparse core gives the change record, the re-embedding list and the stretch descriptor in places
that its later calls may overwrite, so the core copies them into its own heap right after the call
that gives them: the two lists right after op `0`, the descriptor right after op `2`
(`wireRawCopyBody`, `wireStretchDescCopyStmt`, `WireChainCoreSelOutCopyKFBL.lean`). This file gives
the procedure that ends the level, `wireSelOutSlotBody`, and its run lemma
`wireSelOutSlotBody_runs`. It writes, from the fresh word `hp` on, the touched edges of the level
batch and of the next batch (`wireCollectTouchedEdgesBody`), and then the twelve words of the slot:
the places and lengths of the four lists, the descriptor and its width, and the batch. The helper
procedures are called through their contracts `wireRawCopyContract` and `wireCollectContract`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

/-- The contract of `wireRawCopyBody`: copy `n = args[0]` words from `src = args[1]` to
`dst = args[2]`, for disjoint ranges below `2 ^ w`. -/
@[expose] def wireRawCopyContract (w : ℕ) : Contract where
  pre args _ := args = [args.getD 0 0, args.getD 1 0, args.getD 2 0] ∧ 1 < 2 ^ w ∧
    args.getD 1 0 + args.getD 0 0 < 2 ^ w ∧ args.getD 2 0 + args.getD 0 0 < 2 ^ w ∧
    (args.getD 1 0 + args.getD 0 0 ≤ args.getD 2 0 ∨ args.getD 2 0 + args.getD 0 0 ≤ args.getD 1 0)
  post args mem _ mem' :=
    (∀ t < args.getD 0 0, mem' (args.getD 2 0 + t) = mem (args.getD 1 0 + t)) ∧
    ∀ a, a < args.getD 2 0 ∨ args.getD 2 0 + args.getD 0 0 ≤ a → mem' a = mem a
  cost args _ := 20 * args.getD 0 0 + 12

theorem wireRawCopyBody_meets {w f : ℕ} {p : Program} (hf : p.procs[f]? = some wireRawCopyBody) :
    MeetsContract w p f (wireRawCopyContract w) := by
  intro args mem pos ω _ hpre
  obtain ⟨hargs, hw, hS, hD, hDisj⟩ := hpre
  obtain ⟨out, cost, hrun, hc, hcopy, hframe⟩ :=
    wireRawCopyBody_runs (p := p) (ω := ω) (mem := mem) (pos := pos) hw hS hD hDisj
  refine ⟨_, hf, .returned 0, out, cost, ?_, ⟨hcopy, hframe⟩, hc⟩
  rw [hargs]
  exact hrun

/-- The contract of `wireCollectTouchedEdgesBody` for a batch `U` on the graph `G`: collect the
touched edges of the batch at `args[0]` into the zero words at `args[1]`. -/
@[expose] def wireCollectContract (w : ℕ) (G : MGraph) (U : List Update) : Contract where
  pre args mem := args = [args.getD 0 0, args.getD 1 0] ∧ 5 < 2 ^ w ∧ ∃ totalWords,
    SmallBatchAt mem (args.getD 0 0) G U totalWords ∧
    (∀ j < totalWords, mem (args.getD 0 0 + j) < 2 ^ w) ∧
    args.getD 0 0 + totalWords ≤ args.getD 1 0 ∧ ZeroFrom mem (args.getD 1 0) ∧
    args.getD 1 0 + U.length < 2 ^ w
  post args mem v mem' := v = (coreBatchTouchedEdges U).length ∧
    ListAt mem' (args.getD 1 0) (coreBatchTouchedEdges U) ∧
    ZeroFrom mem' (args.getD 1 0 + (coreBatchTouchedEdges U).length) ∧
    ∀ a < args.getD 1 0, mem' a = mem a
  cost _ _ := 60 * U.length + 35

theorem wireCollectTouchedEdgesBody_meets {w f : ℕ} {p : Program} (G : MGraph) (U : List Update)
    (hf : p.procs[f]? = some wireCollectTouchedEdgesBody) :
    MeetsContract w p f (wireCollectContract w G U) := by
  intro args mem pos ω _ hpre
  obtain ⟨hargs, hw, totalWords, hB, hBW, hBLe, hz, hRoom⟩ := hpre
  obtain ⟨out, cost, hrun, hc, hlist, hz', hframe⟩ :=
    wireCollectTouchedEdgesBody_runs (p := p) (ω := ω) (pos := pos) hB hBW hBLe hz hRoom hw
  refine ⟨_, hf, .returned (coreBatchTouchedEdges U).length, out, cost, ?_,
    ⟨rfl, hlist, hz', hframe⟩, hc⟩
  rw [hargs]
  exact hrun

/-- A statement with a known normal run, followed by more statements: the forward form. -/
theorem runs_seq_runs_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt} {st st₁ : State}
    {c₁ k T : ℕ} {Q : Outcome → State → Prop}
    (h₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (hrest : ∃ o st' c₂, Runs w p ω s₂ st₁ o st' c₂ ∧ Q o st' ∧ (k + c₁ + 1) + c₂ ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s₁ s₂) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c₂, h₂, hq, hc⟩ := hrest
  exact ⟨o, st', c₁ + c₂ + 1, runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, h₂, rfl⟩), hq, by omega⟩

/-- Fill one select-output slot. Arguments: `slot, hp, fDelPtr, fDelLen, reembPtr, reembLen,
descPtr, Lw, uPtr, uWords, nextPtr`. It writes, from `hp` on, the touched edges of the batches at
`uPtr` and at `nextPtr`. Then it stores the twelve words of the slot and returns the first free
word. -/
@[expose] def wireSelOutSlotBody (collectProc : ℕ) : Stmt :=
  .call 11 collectProc [.reg 8, .reg 1] ;;
  .assign 12 (.bin .add (.reg 1) (.reg 11)) ;;
  .call 13 collectProc [.reg 10, .reg 12] ;;
  .store (.bin .add (.reg 0) (.const 0)) (.reg 1) ;;
  .store (.bin .add (.reg 0) (.const 1)) (.reg 11) ;;
  .store (.bin .add (.reg 0) (.const 2)) (.reg 2) ;;
  .store (.bin .add (.reg 0) (.const 3)) (.reg 3) ;;
  .store (.bin .add (.reg 0) (.const 4)) (.reg 12) ;;
  .store (.bin .add (.reg 0) (.const 5)) (.reg 13) ;;
  .store (.bin .add (.reg 0) (.const 6)) (.reg 4) ;;
  .store (.bin .add (.reg 0) (.const 7)) (.reg 5) ;;
  .store (.bin .add (.reg 0) (.const 8)) (.reg 6) ;;
  .store (.bin .add (.reg 0) (.const 9)) (.reg 7) ;;
  .store (.bin .add (.reg 0) (.const 10)) (.reg 8) ;;
  .store (.bin .add (.reg 0) (.const 11)) (.reg 9) ;;
  .ret (.bin .add (.reg 12) (.reg 13))

theorem wireSelOutSlotBody_noRand (collectProc : ℕ) : (wireSelOutSlotBody collectProc).NoRand := by
  simp [wireSelOutSlotBody, Stmt.NoRand]

/-- What `wireSelOutSlotBody` leaves: the slot at `slot` holds the twelve words, the touched edges
`uG` and `uS` lie at `hp` and right after, no other word below `hp` changes, and every word from
the returned pointer on is zero. -/
@[expose] def SelOutSlotPost (mem out : ℕ → ℕ) (slot hp fDelPtr fDelLen reembPtr reembLen descPtr
    Lw uPtr uWords : ℕ) (uG uS : List ℕ) : Prop :=
  out (slot + 0) = hp ∧ out (slot + 1) = uG.length ∧
  out (slot + 2) = fDelPtr ∧ out (slot + 3) = fDelLen ∧
  out (slot + 4) = hp + uG.length ∧ out (slot + 5) = uS.length ∧
  out (slot + 6) = reembPtr ∧ out (slot + 7) = reembLen ∧
  out (slot + 8) = descPtr ∧ out (slot + 9) = Lw ∧
  out (slot + 10) = uPtr ∧ out (slot + 11) = uWords ∧
  ListAt out hp uG ∧ ListAt out (hp + uG.length) uS ∧
  (∀ a < hp, (a < slot ∨ slot + 12 ≤ a) → out a = mem a) ∧
  ZeroFrom out (hp + uG.length + uS.length)

/-- Twelve stores into `[slot, slot + 12)` leave every other word. -/
theorem update12_apply_of_out {m : ℕ → ℕ} {slot a : ℕ} {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : ℕ}
    (h : a < slot ∨ slot + 12 ≤ a) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update m (slot + 0) v0) (slot + 1) v1) (slot + 2) v2)
      (slot + 3) v3) (slot + 4) v4) (slot + 5) v5) (slot + 6) v6) (slot + 7) v7) (slot + 8) v8)
      (slot + 9) v9) (slot + 10) v10) (slot + 11) v11 a = m a := by
  have h0 : a ≠ slot + 0 := by omega
  have h1 : a ≠ slot + 1 := by omega
  have h2 : a ≠ slot + 2 := by omega
  have h3 : a ≠ slot + 3 := by omega
  have h4 : a ≠ slot + 4 := by omega
  have h5 : a ≠ slot + 5 := by omega
  have h6 : a ≠ slot + 6 := by omega
  have h7 : a ≠ slot + 7 := by omega
  have h8 : a ≠ slot + 8 := by omega
  have h9 : a ≠ slot + 9 := by omega
  have h10 : a ≠ slot + 10 := by omega
  have h11 : a ≠ slot + 11 := by omega
  rw [Function.update_of_ne h11, Function.update_of_ne h10, Function.update_of_ne h9,
    Function.update_of_ne h8, Function.update_of_ne h7, Function.update_of_ne h6,
    Function.update_of_ne h5, Function.update_of_ne h4, Function.update_of_ne h3,
    Function.update_of_ne h2, Function.update_of_ne h1, Function.update_of_ne h0]

/-- The twelve slot stores at the end of `wireSelOutSlotBody` give `SelOutSlotPost`, from the facts
on the memory before them. -/
theorem selOutSlotPost_of_stores {mem m : ℕ → ℕ} {slot hp fDelPtr fDelLen reembPtr reembLen
      descPtr Lw uPtr uWords : ℕ} {uG uS : List ℕ} {v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11 : ℕ}
    (hv0 : v0 = hp) (hv1 : v1 = uG.length) (hv2 : v2 = fDelPtr) (hv3 : v3 = fDelLen)
    (hv4 : v4 = hp + uG.length) (hv5 : v5 = uS.length) (hv6 : v6 = reembPtr)
    (hv7 : v7 = reembLen) (hv8 : v8 = descPtr) (hv9 : v9 = Lw) (hv10 : v10 = uPtr)
    (hv11 : v11 = uWords)
    (hSlot : slot + 12 ≤ hp)
    (hlo : ∀ a < hp, (a < slot ∨ slot + 12 ≤ a) → m a = mem a)
    (hG : ListAt m hp uG) (hS : ListAt m (hp + uG.length) uS)
    (hz : ZeroFrom m (hp + uG.length + uS.length)) :
    SelOutSlotPost mem
      (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update (Function.update (Function.update (Function.update
        (Function.update (Function.update m (slot + 0) v0) (slot + 1) v1) (slot + 2) v2)
        (slot + 3) v3) (slot + 4) v4) (slot + 5) v5) (slot + 6) v6) (slot + 7) v7) (slot + 8) v8)
        (slot + 9) v9) (slot + 10) v10) (slot + 11) v11)
      slot hp fDelPtr fDelLen reembPtr reembLen descPtr Lw uPtr uWords uG uS := by
  subst v0 v1 v2 v3 v4 v5 v6 v7 v8 v9 v10 v11
  refine ⟨by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp,
    by simp, by simp, fun i hi => ?_, fun i hi => ?_, fun a ha hs => ?_, fun a ha => ?_⟩
  · rw [update12_apply_of_out (slot := slot) (a := hp + i) (Or.inr (by omega))]; exact hG i hi
  · rw [update12_apply_of_out (slot := slot) (a := hp + uG.length + i) (Or.inr (by omega))]
    exact hS i hi
  · rw [update12_apply_of_out hs]; exact hlo a ha hs
  · rw [update12_apply_of_out (slot := slot) (a := a) (Or.inr (by omega))]; exact hz a ha

set_option maxHeartbeats 800000 in
/-- One run of `wireSelOutSlotBody` with the collector at `collectProc`. The two batches and the
slot lie below `hp`, the memory is zero from `hp` on, and the arguments are machine words. The run
costs at most a constant per batch entry, and it leaves `SelOutSlotPost`. -/
theorem wireSelOutSlotBody_runs {w collectProc slot hp fDelPtr fDelLen reembPtr reembLen descPtr
      Lw uPtr uWords nextPtr nextWords pos : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ} {G GS : MGraph} {U US : List Update}
    (hw : 5 < 2 ^ w)
    (hColl : p.procs[collectProc]? = some wireCollectTouchedEdgesBody)
    (hU : SmallBatchAt mem uPtr G U uWords) (hUW : ∀ t < uWords, mem (uPtr + t) < 2 ^ w)
    (hULe : uPtr + uWords ≤ hp)
    (hUS : SmallBatchAt mem nextPtr GS US nextWords)
    (hUSW : ∀ t < nextWords, mem (nextPtr + t) < 2 ^ w) (hUSLe : nextPtr + nextWords ≤ hp)
    (hSlot : slot + 12 ≤ hp) (hz : ZeroFrom mem hp)
    (hRoom : hp + U.length + US.length < 2 ^ w) :
    ∃ (out : State) (cost : ℕ),
      Runs w p ω (wireSelOutSlotBody collectProc)
        (startState [slot, hp, fDelPtr, fDelLen, reembPtr, reembLen, descPtr, Lw, uPtr, uWords,
          nextPtr] mem pos)
        (.returned (hp + (coreBatchTouchedEdges U).length + (coreBatchTouchedEdges US).length))
        out cost ∧
      cost ≤ 60 * (U.length + US.length) + 300 ∧
      SelOutSlotPost mem out.mem slot hp fDelPtr fDelLen reembPtr reembLen descPtr Lw uPtr uWords
        (coreBatchTouchedEdges U) (coreBatchTouchedEdges US) := by
  have hCollU := wireCollectTouchedEdgesBody_meets (w := w) G U hColl
  have hCollS := wireCollectTouchedEdgesBody_meets (w := w) GS US hColl
  have hTLU := coreBatchTouchedEdges_length_le U
  have hTLS := coreBatchTouchedEdges_length_le US
  suffices h : ∃ o st' cost, Runs w p ω (wireSelOutSlotBody collectProc)
      (startState [slot, hp, fDelPtr, fDelLen, reembPtr, reembLen, descPtr, Lw, uPtr, uWords,
        nextPtr] mem pos) o st' cost ∧
      (o = .returned (hp + (coreBatchTouchedEdges U).length + (coreBatchTouchedEdges US).length) ∧
        SelOutSlotPost mem st'.mem slot hp fDelPtr fDelLen reembPtr reembLen descPtr Lw uPtr uWords
          (coreBatchTouchedEdges U) (coreBatchTouchedEdges US)) ∧
      0 + cost ≤ 60 * (U.length + US.length) + 300 by
    obtain ⟨o, st', cost, hr, ⟨rfl, hpost⟩, hc⟩ := h
    exact ⟨st', cost, hr, by omega, hpost⟩
  unfold wireSelOutSlotBody
  refine runs_seq_call_le hCollU (by eval_expr) (by wram_words) ?_ ?_
  · simp only [wireCollectContract, List.getD_cons_zero, List.getD_cons_succ, startState]
    exact ⟨by simp, hw, uWords, hU, hUW, hULe, hz, by omega⟩
  intro v4 m4 pos4 ⟨hv4, hl4, hz4, hf4⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ, startState] at hv4 hl4 hz4 hf4
  have h4lo : ∀ a < hp, m4 a = mem a := fun a ha => hf4 a ha
  wram_step
  refine runs_seq_call_le hCollS (by eval_expr) (by simp only [hv4]; wram_words) ?_ ?_
  · simp only [wireCollectContract, List.getD_cons_zero, List.getD_cons_succ, hv4]
    refine ⟨by simp, hw, nextWords, smallBatchAt_of_agree hUS (fun x _ hx => h4lo x (by omega)),
      fun j hj => by rw [h4lo _ (by omega)]; exact hUSW j hj, by omega,
      fun a ha => hz4 a (by omega), by omega⟩
  intro v5 m5 pos5 ⟨hv5, hl5, hz5, hf5⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ, hv4] at hv5 hl5 hz5 hf5
  wram_run
  · subst hv4 hv5
    have hlt : ∀ a < hp, (a < slot ∨ slot + 12 ≤ a) → m5 a = mem a := fun a ha _ => by
      rw [hf5 a (by omega)]; exact h4lo a ha
    dsimp only
    refine ⟨rfl, selOutSlotPost_of_stores ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hSlot hlt
      (fun i hi => by rw [hf5 (hp + i) (by omega)]; exact hl4 i hi) hl5 hz5⟩
    iterate 12 rfl
  · subst hv4 hv5
    simp only [wireCollectContract]
    wram_cost

end MinCostFlow.MinRatio
