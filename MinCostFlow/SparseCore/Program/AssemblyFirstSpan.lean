module

public import MinCostFlow.SparseCore.Program.RestartLoopDefs
public import MinCostFlow.SparseCore.Program.SpanBucket
public import WordRAM.Logic

import WordRAM.Tactic

/-!
# First-phase calls to P6's bucket spanners (`AssemblyFirstSpan`)

During the first phase of a branch step, after P5 computes the bundle batch `U_B (C, b)` of each
touched active slot `s` (as a `BatchAt` block of `W` words at `batchPtr`), the program runs
operation `1` of P6's `bucketSpannerDS` (`bucketSpanUpdateStmt`) on each slot and records the
address `hOut = hp + W` of the 7-word output header `[uhPtr, |U_H|, uhWords, dPtr, |D|, rPtr, |R|]`
written by each call.

This file defines and verifies the deterministic Word-RAM procedure `asmFirstSpanUpdStmt fUpd`
on `[spanTbl, descPtr, n, h]`:
* `descPtr` holds `n` 3-word descriptors `[slot_i, batchPtr_i, W_i]` (produced by P5's step,
  captured by the named layout predicate `SpanUpdTasksAt`).
* `[h, h + n)` receives the `n` output-header pointers `hOut_i = hp_i + W_i`, so the later output-
  edge selector and embedding-table copy can read each slot's `U_H`, `D`, and `R` lists directly.
* Each call advances slot `slot_i` in `bucketSpannerRep P cap` (`spanUpdAfter`), with full frame,
  footprint growth inside `[h + n, o.value)`, `ZeroFrom`, space bound `n + ∑ dsUpdateOpSpace`, and
  amortized cost bound against `bucketPhi` (`asmFirstSpanUpd_runs`).

For newly active pairs, P6 operation `0` activation over a list of exported bundle graphs is
already verified by `Restart.restartLoop_triple` (`RestartLoop.lean`).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

/-! ## Procedure and pure model helpers -/

@[expose] public section

/-- One bucket-spanner update task: slot index, batch address, and batch word count `W`. -/
structure SpanUpdTask where
  slot : ℕ
  batchPtr : ℕ
  W : ℕ

/-- The `n` update descriptors `[slot, batchPtr, W]` stored consecutively at `descPtr`. -/
def SpanUpdTasksAt (mem : ℕ → ℕ) (descPtr : ℕ) (tasks : List SpanUpdTask) : Prop :=
  ∀ (i : ℕ) (hi : i < tasks.length),
    mem (descPtr + 3 * i) = (tasks[i]'hi).slot ∧
    mem (descPtr + 3 * i + 1) = (tasks[i]'hi).batchPtr ∧
    mem (descPtr + 3 * i + 2) = (tasks[i]'hi).W

/-- Abstract bucket-spanner state after applying the update batches of `tasks` (read from `mem₀`). -/
noncomputable def spanUpdAfter (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) : List SpanUpdTask → BucketSpannerState cap
  | [] => S6
  | t :: ts =>
    let S' := if hs : t.slot < cap then
      match S6 ⟨t.slot, hs⟩ with
      | some d =>
        let U := (decodeBatch mem₀ t.batchPtr (d.state P).G).1
        S6.set ⟨t.slot, hs⟩ (some ⟨d.G₀, d.Us ++ [U]⟩)
      | none => S6
    else S6
    spanUpdAfter P S' mem₀ ts

/-- Loop body of `asmFirstSpanUpdStmt`: reads descriptor `i` (`slot`, `batchPtr`, `W`), stores
`hOut = hp + W` at `h + i`, and calls `fUpd [spanTbl, slot, batchPtr, W, hp]`.
Registers: `0 = spanTbl`, `1 = descPtr`, `2 = n`, `3 = h`, `4 = hp`, `5 = i`, `6..8` scratch. -/
def asmFirstSpanUpdBody (fUpd : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5)))) ;;
  .assign 7 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5))) (.const 1))) ;;
  .assign 8 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5))) (.const 2))) ;;
  .store (.bin .add (.reg 3) (.reg 5)) (.bin .add (.reg 4) (.reg 8)) ;;
  .call 4 fUpd [.reg 0, .reg 6, .reg 7, .reg 8, .reg 4]

/-- **First-phase bucket-spanner update loop**, `[spanTbl, descPtr, n, h]`: allocates the `n`-word
output-header pointer array at `[h, h + n)`, runs P6 op `1` on every task in `descPtr`, stores
each call's `hOut = hp + W` at `h + i`, and returns the final heap pointer. -/
def asmFirstSpanUpdStmt (fUpd : ℕ) : Stmt :=
  .assign 4 (.bin .add (.reg 3) (.reg 2)) ;;
  forRange 5 (.const 0) (.reg 2) (asmFirstSpanUpdBody fUpd) ;;
  .ret (.reg 4)

/-- The per-task space bound read on the initial state `S6` and initial memory `mem₀`. -/
noncomputable def spanTaskSpace (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (t : SpanUpdTask) : ℕ :=
  if hs : t.slot < cap then
    match S6 ⟨t.slot, hs⟩ with
    | some d => dsUpdateOpSpace P d [0, t.batchPtr, t.W, 0] mem₀
    | none => 0
  else 0

/-- The per-task amortized cost bound read on the initial state `S6` and initial memory `mem₀`. -/
noncomputable def spanTaskCost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (t : SpanUpdTask) : ℕ :=
  if hs : t.slot < cap then
    match S6 ⟨t.slot, hs⟩ with
    | some d => dsUpdateAmortCost P d [0, t.batchPtr, t.W, 0] mem₀ + 20
    | none => 0
  else 0

/-- Named interface for the batch descriptors that P5's step writes for P6. -/
structure AsmFirstBunStepOut (P : DSParams) (cap : ℕ) (S6 : BucketSpannerState cap)
    (descPtr h : ℕ) (tasks : List SpanUpdTask) (mem : ℕ → ℕ) : Prop where
  htasks : SpanUpdTasksAt mem descPtr tasks
  hnd : (tasks.map SpanUpdTask.slot).Nodup
  hdesc_le : descPtr + 3 * tasks.length ≤ h
  hslots : ∀ t ∈ tasks, ∃ (hs : t.slot < cap) (d : DSHist), S6 ⟨t.slot, hs⟩ = some d ∧
    DSUpdatePre P d [0, t.batchPtr, t.W, h] mem

end

/-! ## Private helper lemmas -/

private lemma decodeUpdate_congr {mem mem' : ℕ → ℕ} {a : ℕ} {G : MGraph}
    (hag : ∀ k < (decodeUpdate mem a G).2, mem' (a + k) = mem (a + k)) :
    decodeUpdate mem' a G = decodeUpdate mem a G := by
  have hlen_pos : 0 < (decodeUpdate mem a G).2 := by
    unfold decodeUpdate
    split_ifs <;> dsimp only <;> omega
  have h0 : mem' a = mem a := by simpa using hag 0 hlen_pos
  unfold decodeUpdate at hag ⊢
  by_cases hc0 : mem a = 0
  · have h1 := hag 1 (by simp [hc0])
    have h2 := hag 2 (by simp [hc0])
    have h3 := hag 3 (by simp [hc0])
    simp [hc0, h0, h1, h2, h3]
  · by_cases hc1 : mem a = 1
    · have h1 := hag 1 (by simp [hc1])
      simp [hc1, h0, h1]
    · have hlen_ge : 5 + mem (a + 3) + mem (a + 4) ≤
          (if mem a = 0 then (Update.insert (mem (a + 1)) (mem (a + 2)) (mem (a + 3)), 4)
           else if mem a = 1 then (Update.delete (mem (a + 1)), 2)
           else
             let v := mem (a + 1); let kt := mem (a + 3); let kh := mem (a + 4)
             let Lt := (readList mem (a + 5) kt).toFinset
             let Lh := (readList mem (a + 5 + kt) kh).toFinset
             if mem a = 2 then (Update.split v (mem (a + 2)) Lt Lh, 5 + kt + kh)
             else (Update.split v (mem (a + 2)) ({e ∈ G.E | G.tail e = v} \ Lt)
               ({e ∈ G.E | G.head e = v} \ Lh), 5 + kt + kh)).2 := by
        simp only [hc0, hc1, ↓reduceIte]
        split_ifs <;> dsimp only <;> omega
      have h1 := hag 1 (by omega)
      have h2 := hag 2 (by omega)
      have h3 := hag 3 (by omega)
      have h4 := hag 4 (by omega)
      have hkt : readList mem' (a + 5) (mem (a + 3)) = readList mem (a + 5) (mem (a + 3)) := by
        unfold readList
        refine List.map_congr_left fun i hi => ?_
        have hi' := List.mem_range.mp hi
        simpa [Nat.add_assoc] using hag (5 + i) (by omega)
      have hkh : readList mem' (a + 5 + mem (a + 3)) (mem (a + 4)) =
          readList mem (a + 5 + mem (a + 3)) (mem (a + 4)) := by
        unfold readList
        refine List.map_congr_left fun i hi => ?_
        have hi' := List.mem_range.mp hi
        simpa [Nat.add_assoc] using hag (5 + mem (a + 3) + i) (by omega)
      simp only [h0, hc0, hc1, ↓reduceIte, h1, h2, h3, h4, hkt, hkh]

private lemma decodeBatchBody_congr {mem mem' : ℕ → ℕ} :
    ∀ (n a : ℕ) (G : MGraph),
      (∀ k < (decodeBatchBody mem n a G).2.sum, mem' (a + k) = mem (a + k)) →
      decodeBatchBody mem' n a G = decodeBatchBody mem n a G
  | 0, _, _, _ => rfl
  | n + 1, a, G, hag => by
    unfold decodeBatchBody at hag ⊢
    simp only [List.sum_cons] at hag
    have hd : decodeUpdate mem' a G = decodeUpdate mem a G :=
      decodeUpdate_congr fun k hk => hag k (by omega)
    rw [hd]
    have hrest : decodeBatchBody mem' n (a + (decodeUpdate mem a G).2)
        (G.applyUpdate (decodeUpdate mem a G).1) =
      decodeBatchBody mem n (a + (decodeUpdate mem a G).2)
        (G.applyUpdate (decodeUpdate mem a G).1) :=
      decodeBatchBody_congr n (a + (decodeUpdate mem a G).2)
        (G.applyUpdate (decodeUpdate mem a G).1) fun k hk => by
          have := hag ((decodeUpdate mem a G).2 + k) (by omega)
          simpa [Nat.add_assoc] using this
    dsimp only
    rw [hrest]

private lemma decodeBatch_congr {mem mem' : ℕ → ℕ} {a W : ℕ} {G : MGraph}
    (hW : W = 1 + (decodeBatch mem a G).2.sum)
    (hag : ∀ k < W, mem' (a + k) = mem (a + k)) :
    decodeBatch mem' a G = decodeBatch mem a G := by
  unfold decodeBatch at hW ⊢
  have h0 : mem' a = mem a := by simpa using hag 0 (by omega)
  rw [h0]
  exact decodeBatchBody_congr (mem a) (a + 1) G fun k hk => by
    have := hag (1 + k) (by omega)
    simpa [Nat.add_assoc] using this

private lemma batchBodyLensAt_congr {mem mem' : ℕ → ℕ} :
    ∀ {a : ℕ} {G : MGraph} {U : List Update} {lens : List ℕ},
      BatchBodyLensAt mem a G U lens →
      (∀ k < lens.sum, mem' (a + k) = mem (a + k)) →
      BatchBodyLensAt mem' a G U lens
  | _, _, [], [], h, _ => h
  | _, _, [], _ :: _, h, _ => h
  | _, _, _ :: _, [], h, _ => h
  | a, G, u :: U, len :: lens, ⟨hu, hrest⟩, hag => by
    simp only [List.sum_cons] at hag
    refine ⟨?_, batchBodyLensAt_congr hrest fun k hk => by
      have := hag (len + k) (by omega); simpa [Nat.add_assoc] using this⟩
    rcases u with ⟨e, x, y⟩ | e | ⟨v, v', St, Sh⟩
    · rcases hu with ⟨rfl, hList⟩
      exact ⟨rfl, fun i hi => (hag i (by simp at hi; omega)).trans (hList i hi)⟩
    · rcases hu with ⟨rfl, hList⟩
      exact ⟨rfl, fun i hi => (hag i (by simp at hi; omega)).trans (hList i hi)⟩
    · rcases hu with ⟨L_t, L_h, hnd1, hnd2, hmt, hmh, rfl, hList⟩ |
        ⟨L_t, L_h, hnd1, hnd2, hmt, hmh, rfl, hList⟩
      · exact Or.inl ⟨L_t, L_h, hnd1, hnd2, hmt, hmh, rfl,
          fun i hi => (hag i (by simp at hi; omega)).trans (hList i hi)⟩
      · exact Or.inr ⟨L_t, L_h, hnd1, hnd2, hmt, hmh, rfl,
          fun i hi => (hag i (by simp at hi; omega)).trans (hList i hi)⟩

private lemma dsUpdatePre_batch_le {P : DSParams} {d : DSHist} {batchPtr W h : ℕ} {mem : ℕ → ℕ}
    (hpre : DSUpdatePre P d [0, batchPtr, W, h] mem) : batchPtr + W ≤ h := by
  obtain ⟨_, _, _, _, heq, _, _, _, hbp, _⟩ := hpre
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨-, rfl, rfl, rfl⟩
  exact hbp

private lemma dsUpdatePre_congr {P : DSParams} {d : DSHist} {batchPtr W h h' : ℕ}
    {mem mem' : ℕ → ℕ}
    (hpre : DSUpdatePre P d [0, batchPtr, W, h] mem) (hle : h ≤ h')
    (hag : ∀ k < W, mem' (batchPtr + k) = mem (batchPtr + k)) :
    DSUpdatePre P d [0, batchPtr, W, h'] mem' ∧
      decodeBatch mem' batchPtr (d.state P).G = decodeBatch mem batchPtr (d.state P).G := by
  obtain ⟨_, _, _, _, heq, hw16, hbl, hW, hbp, hwd, hbv, hds, hcaps, hspl, hgen, hlen, hq, hok⟩ :=
    hpre
  simp only [List.cons.injEq, and_true] at heq
  rcases heq with ⟨-, rfl, rfl, rfl⟩
  simp only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
    Option.getD_some] at hbl hW hbv hds hcaps hspl hgen hlen hok
  have hdec := decodeBatch_congr hW hag
  refine ⟨⟨0, batchPtr, W, h', rfl, hw16, ?_, ?_, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hq, ?_⟩,
    hdec⟩
  · simp only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec]
    exact batchBodyLensAt_congr hbl fun k hk => by
      have := hag (1 + k) (by omega); simpa [Nat.add_assoc] using this
  · simp only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec]
    exact hW
  · intro i hi; rw [hag i hi]; exact hwd i hi
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hbv
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hds
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hcaps
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hspl
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hgen
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hlen
  · simpa only [opBatch, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
      Option.getD_some, hdec] using hok

private lemma spanUpdAfter_append (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (ts₁ ts₂ : List SpanUpdTask) :
    spanUpdAfter P S6 mem₀ (ts₁ ++ ts₂) = spanUpdAfter P (spanUpdAfter P S6 mem₀ ts₁) mem₀ ts₂ := by
  induction ts₁ generalizing S6 with
  | nil => rfl
  | cons t ts ih => exact ih _

private lemma spanUpdAfter_unchanged (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) {ts : List SpanUpdTask} {j : Fin cap}
    (hnot : j.1 ∉ ts.map SpanUpdTask.slot) :
    spanUpdAfter P S6 mem₀ ts j = S6 j := by
  induction ts generalizing S6 with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hnot
    rw [spanUpdAfter, ih _ hnot.2]
    by_cases hs : t.slot < cap
    · simp only [hs, ↓reduceDIte]
      cases S6 ⟨t.slot, hs⟩ with
      | none => rfl
      | some d =>
        have hne : j ≠ ⟨t.slot, hs⟩ := fun h => hnot.1 (congrArg Fin.val h)
        simp [BucketSpannerState.set, Function.update_of_ne hne]
    · simp [hs]

private lemma spanUpdAfter_take_succ (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) {tasks : List SpanUpdTask} {i : ℕ} (hi : i < tasks.length)
    (hnd : (tasks.map SpanUpdTask.slot).Nodup)
    (hs : (tasks[i]'hi).slot < cap) {d : DSHist} (hd : S6 ⟨(tasks[i]'hi).slot, hs⟩ = some d) :
    spanUpdAfter P S6 mem₀ (tasks.take (i + 1)) =
      (spanUpdAfter P S6 mem₀ (tasks.take i)).set ⟨(tasks[i]'hi).slot, hs⟩
        (some ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ (tasks[i]'hi).batchPtr (d.state P).G).1]⟩) := by
  rw [List.take_succ_eq_append_getElem hi, spanUpdAfter_append]
  have hnot : (tasks[i]'hi).slot ∉ ((tasks.take i).map SpanUpdTask.slot) := by
    intro hm
    rw [List.mem_map] at hm
    obtain ⟨t', ht', heq⟩ := hm
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht'
    rw [List.length_take] at hk
    have hklt : k < i := by omega
    have hklen : k < tasks.length := by omega
    have hget : (tasks.take i)[k]'(by rw [List.length_take]; omega) = tasks[k]'hklen :=
      List.getElem_take
    rw [hget] at heq
    have hidx : k = i := (List.Nodup.getElem_inj_iff hnd (i := k) (j := i)
      (hi := by simp [hklen]) (hj := by simp [hi])).mp (by simpa using heq)
    omega
  have hcur : spanUpdAfter P S6 mem₀ (tasks.take i) ⟨(tasks[i]'hi).slot, hs⟩ = some d := by
    rw [spanUpdAfter_unchanged P S6 mem₀ hnot, hd]
  simp only [spanUpdAfter, hs, ↓reduceDIte, hcur]

private lemma dsUpdateAmortCost_eq_of_decode {P : DSParams} {d : DSHist} {b₁ b₂ batchPtr W h₁ h₂ : ℕ}
    {mem₁ mem₂ : ℕ → ℕ}
    (hdec : decodeBatch mem₁ batchPtr (d.state P).G = decodeBatch mem₂ batchPtr (d.state P).G) :
    dsUpdateAmortCost P d [b₁, batchPtr, W, h₁] mem₁ =
      dsUpdateAmortCost P d [b₂, batchPtr, W, h₂] mem₂ := by
  simp only [dsUpdateAmortCost, opBatch, opWords, List.getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, hdec]

private lemma dsUpdateOpSpace_eq_of_decode {P : DSParams} {d : DSHist} {b₁ b₂ batchPtr W h₁ h₂ : ℕ}
    {mem₁ mem₂ : ℕ → ℕ}
    (hdec : decodeBatch mem₁ batchPtr (d.state P).G = decodeBatch mem₂ batchPtr (d.state P).G) :
    dsUpdateOpSpace P d [b₁, batchPtr, W, h₁] mem₁ =
      dsUpdateOpSpace P d [b₂, batchPtr, W, h₂] mem₂ := by
  simp only [dsUpdateOpSpace, opBatch, opWords, List.getD, List.getElem?_cons_succ,
    List.getElem?_cons_zero, Option.getD_some, hdec]

/-! ## Verification of `asmFirstSpanUpdStmt` -/

public section

theorem asmFirstSpanUpdStmt_noRand (fUpd : ℕ) : (asmFirstSpanUpdStmt fUpd).NoRand := by
  simp [asmFirstSpanUpdStmt, asmFirstSpanUpdBody, forRange, forUp, Stmt.NoRand]

/-- Loop invariant after `i` rounds of `asmFirstSpanUpdStmt`. -/
private def SpanUpdLoopInv (P : DSParams) {cap : ℕ} (spanTbl descPtr h : ℕ)
    (S6 : BucketSpannerState cap) (x6 : (bucketSpannerRep P cap).τ) (tasks : List SpanUpdTask)
    (mem₀ : ℕ → ℕ) (i : ℕ) (st : State) : Prop :=
  st.regs 0 = spanTbl ∧ st.regs 1 = descPtr ∧ st.regs 2 = tasks.length ∧ st.regs 3 = h ∧
  st.regs 5 = i ∧
  h + tasks.length ≤ st.regs 4 ∧
  st.regs 4 ≤ h + tasks.length + ((tasks.take i).map (spanTaskSpace P S6 mem₀)).sum ∧
  ZeroFrom st.mem (st.regs 4) ∧
  (∀ a < h, ¬ (bucketSpannerRep P cap).foot spanTbl x6 a → st.mem a = mem₀ a) ∧
  (∀ j < i, h + tasks.length ≤ st.mem (h + j) ∧ st.mem (h + j) ≤ st.regs 4) ∧
  (∀ j < i, specPhi P (spanUpdAfter P S6 mem₀ (tasks.take (j + 1))) ≤
    spanTaskCost P S6 mem₀ (tasks.getD j ⟨0, 0, 0⟩) +
      specPhi P (spanUpdAfter P S6 mem₀ (tasks.take j))) ∧
  ∃ x6i, (bucketSpannerRep P cap).rep spanTbl (spanUpdAfter P S6 mem₀ (tasks.take i)) x6i st.mem ∧
    ∀ a, (bucketSpannerRep P cap).foot spanTbl x6i a →
      (bucketSpannerRep P cap).foot spanTbl x6 a ∨ (h + tasks.length ≤ a ∧ a < st.regs 4)

private noncomputable def spanUpdStepCost (P : DSParams) {cap : ℕ} (S6 : BucketSpannerState cap)
    (mem₀ : ℕ → ℕ) (tasks : List SpanUpdTask) (i : ℕ) : ℕ :=
  80 + (spanTaskCost P S6 mem₀ (tasks.getD i ⟨0, 0, 0⟩) +
    specPhi P (spanUpdAfter P S6 mem₀ (tasks.take i)) -
    specPhi P (spanUpdAfter P S6 mem₀ (tasks.take (i + 1))))

/-- **Correctness, frame, space, and amortized cost of `asmFirstSpanUpdStmt`.** Given a program
containing `bucketSpannerProcs P.impl bSpan`, `asmFirstSpanUpdStmt (bSpan + bsIdxOp0 + 1)` updates
every slot listed in `tasks`, records each slot's output header address `hOut_i` at `h + i`, keeps
the frame below `h`, grows the spanner footprint inside `[h + tasks.length, o.value)`, and meets
the amortized cost bound against `bucketPhi`. -/
theorem asmFirstSpanUpd_runs (P : DSParams) {cap : ℕ} {p : Program} {bSpan : ℕ}
    (hp : p.HasAt bSpan (bucketSpannerProcs P.impl bSpan))
    {spanTbl descPtr h : ℕ} {S6 : BucketSpannerState cap} {x6 : (bucketSpannerRep P cap).τ}
    {tasks : List SpanUpdTask} {mem₀ : ℕ → ℕ} {pos : ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ P.w)
    (hrep : (bucketSpannerRep P cap).rep spanTbl S6 x6 mem₀)
    (hfoot : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6 a → a < h)
    (hBun : AsmFirstBunStepOut P cap S6 descPtr h tasks mem₀)
    (hdesc_free : ∀ a, descPtr ≤ a → a < descPtr + 3 * tasks.length →
      ¬ (bucketSpannerRep P cap).foot spanTbl x6 a)
    (hbatch_free : ∀ t ∈ tasks, ∀ a, t.batchPtr ≤ a → a < t.batchPtr + t.W →
      ¬ (bucketSpannerRep P cap).foot spanTbl x6 a)
    (hz : ZeroFrom mem₀ h)
    (hspace : h + tasks.length + (tasks.map (spanTaskSpace P S6 mem₀)).sum < 2 ^ P.w) :
    ∃ o st' c x',
      Runs P.w p ω (asmFirstSpanUpdStmt (bSpan + bsIdxOp0 + 1))
        (startState [spanTbl, descPtr, tasks.length, h] mem₀ pos) o st' c ∧
      (bucketSpannerRep P cap).rep spanTbl (spanUpdAfter P S6 mem₀ tasks) x' st'.mem ∧
      (∀ i < tasks.length, h + tasks.length ≤ st'.mem (h + i) ∧ st'.mem (h + i) ≤ o.value) ∧
      h + tasks.length ≤ o.value ∧
      o.value ≤ h + tasks.length + (tasks.map (spanTaskSpace P S6 mem₀)).sum ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, ¬ (bucketSpannerRep P cap).foot spanTbl x6 a → st'.mem a = mem₀ a) ∧
      (∀ a, (bucketSpannerRep P cap).foot spanTbl x' a →
        (bucketSpannerRep P cap).foot spanTbl x6 a ∨ (h + tasks.length ≤ a ∧ a < o.value)) ∧
      c + (bucketSpannerRep P cap).phi spanTbl x' st'.mem ≤
        (tasks.map fun t => spanTaskCost P S6 mem₀ t + 95).sum + 40 +
          (bucketSpannerRep P cap).phi spanTbl x6 mem₀ := by
  have hw1 : 1 < 2 ^ P.w := by omega
  have hImp := bucketSpannerDS_implements P cap hp
  have hn_lt : tasks.length < 2 ^ P.w := by omega
  have hh_lt : h < 2 ^ P.w := by omega
  have hhn_lt : h + tasks.length < 2 ^ P.w := by omega
  have hdesc_lt : descPtr + 3 * tasks.length < 2 ^ P.w := by have := hBun.hdesc_le; omega
  -- One iteration of the loop body.
  have hbody : ∀ i < tasks.length,
      Triple P.w p (SpanUpdLoopInv P spanTbl descPtr h S6 x6 tasks mem₀ i)
        (asmFirstSpanUpdBody (bSpan + bsIdxOp0 + 1))
        (normalPost fun st₁ =>
          SpanUpdLoopInv P spanTbl descPtr h S6 x6 tasks mem₀ (i + 1)
              { st₁ with regs := Function.update st₁.regs 5 (i + 1) } ∧
            st₁.regs 5 = i)
        (fun _ => spanUpdStepCost P S6 mem₀ tasks i) := by
    intro i hi st ω' hInv
    obtain ⟨hr0, hr1, hr2, hr3, hr5, hhp_lo, hhp_hi, hzhp, hfr, houts, hph, x6i, hrepi, hfooti⟩ :=
      hInv
    set t := tasks[i]'hi with ht_def
    have htmem : t ∈ tasks := List.getElem_mem hi
    obtain ⟨hslot, d, hdS6, hpre0⟩ := hBun.hslots t htmem
    have hpre0' := hpre0
    obtain ⟨_, _, _, _, heq0, -, -, -, hbp_le, -, -, -, -, -, -, -, -, -⟩ := hpre0'
    simp only [List.cons.injEq, and_true] at heq0
    rcases heq0 with ⟨-, -, -, -⟩
    have hdesc_i := hBun.htasks i hi
    have hmem_slot : st.mem (descPtr + 3 * i) = t.slot := by
      have hlt : descPtr + 3 * i < h := by have := hBun.hdesc_le; omega
      rw [hfr _ hlt (hdesc_free _ (by omega) (by omega))]; exact hdesc_i.1
    have hmem_bp : st.mem (descPtr + 3 * i + 1) = t.batchPtr := by
      have hlt : descPtr + 3 * i + 1 < h := by have := hBun.hdesc_le; omega
      rw [hfr _ hlt (hdesc_free _ (by omega) (by omega))]; exact hdesc_i.2.1
    have hmem_W : st.mem (descPtr + 3 * i + 2) = t.W := by
      have hlt : descPtr + 3 * i + 2 < h := by have := hBun.hdesc_le; omega
      rw [hfr _ hlt (hdesc_free _ (by omega) (by omega))]; exact hdesc_i.2.2
    have htake_sum : ((tasks.take (i + 1)).map (spanTaskSpace P S6 mem₀)).sum =
        ((tasks.take i).map (spanTaskSpace P S6 mem₀)).sum + spanTaskSpace P S6 mem₀ t := by
      rw [List.take_succ_eq_append_getElem hi, List.map_append, List.sum_append,
        List.map_singleton, List.sum_singleton]
    have htake_le : ((tasks.take (i + 1)).map (spanTaskSpace P S6 mem₀)).sum ≤
        (tasks.map (spanTaskSpace P S6 mem₀)).sum := by
      have hsplit : ((tasks.take (i + 1)).map (spanTaskSpace P S6 mem₀)).sum +
          ((tasks.drop (i + 1)).map (spanTaskSpace P S6 mem₀)).sum =
          (tasks.map (spanTaskSpace P S6 mem₀)).sum := by
        rw [← List.sum_append, ← List.map_append, List.take_append_drop]
      omega
    have hsp_eq : spanTaskSpace P S6 mem₀ t = dsUpdateOpSpace P d [0, t.batchPtr, t.W, 0] mem₀ := by
      unfold spanTaskSpace; simp only [hslot, ↓reduceDIte, hdS6]
    have hW_le_sp : t.W ≤ spanTaskSpace P S6 mem₀ t := by
      rw [hsp_eq]; unfold dsUpdateOpSpace opWords
      simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some]
      omega
    have hhp_lt : st.regs 4 < 2 ^ P.w := by omega
    have hhpW_lt : st.regs 4 + t.W < 2 ^ P.w := by omega
    have hnot_i : t.slot ∉ (tasks.take i).map SpanUpdTask.slot := by
      intro hm
      rw [List.mem_map] at hm
      obtain ⟨t', ht', heq⟩ := hm
      obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.mp ht'
      rw [List.length_take] at hk
      have hklen : k < tasks.length := by omega
      have hget : (tasks.take i)[k]'(by rw [List.length_take]; omega) = tasks[k]'hklen :=
        List.getElem_take
      rw [hget] at heq
      have hidx : k = i := (List.Nodup.getElem_inj_iff hBun.hnd (i := k) (j := i)
        (hi := by simp [hklen]) (hj := by simp [hi])).mp (by simpa using heq)
      omega
    have hcurS : spanUpdAfter P S6 mem₀ (tasks.take i) ⟨t.slot, hslot⟩ = some d := by
      rw [spanUpdAfter_unchanged P S6 mem₀ hnot_i, hdS6]
    -- State after the 3 assignments and 1 store to `h + i`.
    set mem₁ := Function.update st.mem (h + i) (st.regs 4 + t.W)
    have hmem₁_ag_foot : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6i a → mem₁ a = st.mem a := by
      intro a ha
      simp only [mem₁]
      rw [Function.update_of_ne]
      rcases hfooti a ha with hf | ⟨hle, _⟩
      · have := hfoot a hf; omega
      · omega
    have hrep₁ : (bucketSpannerRep P cap).rep spanTbl
        (spanUpdAfter P S6 mem₀ (tasks.take i)) x6i mem₁ :=
      (bucketSpannerRep_local P cap spanTbl _ x6i st.mem mem₁
        (fun a ha => (hmem₁_ag_foot a ha).symm)).1 hrepi
    have hbp_le : t.batchPtr + t.W ≤ h := dsUpdatePre_batch_le hpre0
    have hbatch_ag : ∀ k < t.W, mem₁ (t.batchPtr + k) = mem₀ (t.batchPtr + k) := by
      intro k hk
      have hlt : t.batchPtr + k < h := by omega
      simp only [mem₁]
      rw [Function.update_of_ne (by omega)]
      exact hfr _ hlt (hbatch_free t htmem _ (by omega) (by omega))
    obtain ⟨hpre₁, hdec₁⟩ := dsUpdatePre_congr hpre0 (show h ≤ st.regs 4 by omega) hbatch_ag
    have hfoot₁ : ∀ a, (bucketSpannerRep P cap).foot spanTbl x6i a → a < st.regs 4 := by
      intro a ha
      rcases hfooti a ha with hf | ⟨_, hlt⟩
      · have := hfoot a hf; omega
      · exact hlt
    have htbl_slot : spanTbl + t.slot < st.regs 4 :=
      bucket_slot_lt_of_foot hfoot₁ hslot
    have hargsW : ∀ a ∈ [spanTbl, t.slot, t.batchPtr, t.W, st.regs 4], a < 2 ^ P.w := by
      intro a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
      rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
    have hz₁ : ZeroFrom mem₁ (st.regs 4) := fun a ha => by
      simp only [mem₁]
      rw [Function.update_of_ne (by omega)]; exact hzhp a ha
    have hsp₁_eq : (bucketSpannerDS P cap).space 1 (spanUpdAfter P S6 mem₀ (tasks.take i))
        [spanTbl, t.slot, t.batchPtr, t.W, st.regs 4] mem₁ = spanTaskSpace P S6 mem₀ t := by
      simp only [bucketSpannerDS, bucketUpdateSpace, List.getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, hslot, ↓reduceDIte]
      change (match spanUpdAfter P S6 mem₀ (tasks.take i) ⟨t.slot, hslot⟩ with
        | some s => dsUpdateOpSpace P s [0, t.batchPtr, t.W, st.regs 4] mem₁ | none => 0) = _
      rw [hcurS, hsp_eq]
      exact dsUpdateOpSpace_eq_of_decode hdec₁
    have hcost₁_eq : (bucketSpannerDS P cap).cost 1 (spanUpdAfter P S6 mem₀ (tasks.take i))
        [spanTbl, t.slot, t.batchPtr, t.W, st.regs 4] mem₁ = spanTaskCost P S6 mem₀ t := by
      simp only [bucketSpannerDS, bucketUpdateCost, List.getD, List.getElem?_cons_succ,
        List.getElem?_cons_zero, Option.getD_some, hslot, ↓reduceDIte]
      change (match spanUpdAfter P S6 mem₀ (tasks.take i) ⟨t.slot, hslot⟩ with
        | some s => dsUpdateAmortCost P s [0, t.batchPtr, t.W, st.regs 4] mem₁ + 20 | none => 0) = _
      unfold spanTaskCost; simp only [hslot, ↓reduceDIte, hdS6, hcurS]
      rw [dsUpdateAmortCost_eq_of_decode hdec₁]
    have hspace₁ : st.regs 4 + (bucketSpannerDS P cap).space 1
        (spanUpdAfter P S6 mem₀ (tasks.take i))
        [spanTbl, t.slot, t.batchPtr, t.W, st.regs 4] mem₁ < 2 ^ P.w := by
      rw [hsp₁_eq]; omega
    obtain ⟨bd, hbd, o₁, st₁, c₁, hrun₁, S', x', hrep', hpost', hresp', hc₁⟩ :=
      hImp.2.2 1 spanTbl _ x6i [spanTbl, t.slot, t.batchPtr, t.W, st.regs 4] mem₁ st.pos ω'
        hargsW rfl hrep₁ ⟨spanTbl, t.slot, t.batchPtr, t.W, st.regs 4, rfl, hslot, d, hcurS, hpre₁⟩
        hfoot₁ hz₁ hspace₁
    obtain ⟨hslot', s0', s1', hcurS', hS'eq, hdsPost⟩ := hpost'
    have hs0_eq : d = s0' := Option.some.inj (hcurS.symm.trans hcurS')
    rcases hs0_eq with rfl
    have hS'_after : S' = spanUpdAfter P S6 mem₀ (tasks.take (i + 1)) := by
      rw [hS'eq, spanUpdAfter_take_succ P S6 mem₀ hi hBun.hnd hslot hdS6]
      have hs1_eq : s1' = ⟨d.G₀, d.Us ++ [(decodeBatch mem₀ t.batchPtr (d.state P).G).1]⟩ := by
        rw [hdsPost.1]; simp only [opBatch, List.getD, List.getElem?_cons_succ,
          List.getElem?_cons_zero, Option.getD_some, hdec₁]
      rw [hs1_eq]
      simp only [List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero, Option.getD_some,
        ht_def]
    rw [hS'_after] at hrep'
    obtain ⟨hlo₁, hhi₁, hz', hfr₁, hft₁⟩ := hresp'
    change st.regs 4 ≤ o₁.value at hlo₁
    change ∀ a < st.regs 4, ¬ (bucketSpannerRep P cap).foot spanTbl x6i a →
      st₁.mem a = mem₁ a at hfr₁
    rw [hsp₁_eq] at hhi₁
    change o₁.value ≤ st.regs 4 + spanTaskSpace P S6 mem₀ t at hhi₁
    have hphi_i := bucketPhi_eq_specPhi hrep₁
    have hphi_i1 := bucketPhi_eq_specPhi hrep'
    rw [hcost₁_eq, hphi_i, hphi_i1] at hc₁
    have hgetD : tasks.getD i ⟨0, 0, 0⟩ = t := List.getD_eq_getElem _ _ hi
    -- Run the 4 setup statements + call.
    have he3 : (Expr.const 3).eval P.w st = some 3 := Expr.eval_const (by omega)
    have he3i : (Expr.bin .mul (.const 3) (.reg 5)).eval P.w st = some (3 * i) :=
      Expr.eval_mul he3 (Expr.eval_reg_of_eq hr5) (by omega)
    have heBase : (Expr.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5))).eval P.w st =
        some (descPtr + 3 * i) :=
      Expr.eval_add (Expr.eval_reg_of_eq hr1) he3i (by omega)
    have heSlot : (Expr.load (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5)))).eval P.w st =
        some t.slot :=
      Expr.eval_load_of_eq heBase hmem_slot
    set rA := Function.update st.regs 6 t.slot
    have heBaseA : (Expr.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5))).eval P.w
        ⟨st.mem, rA, st.pos⟩ = some (descPtr + 3 * i) :=
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rA, hr1]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [rA, hr5]))
          (by omega)) (by omega)
    have heBp : (Expr.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5)))
        (.const 1))).eval P.w ⟨st.mem, rA, st.pos⟩ = some t.batchPtr :=
      Expr.eval_load_of_eq (Expr.eval_add heBaseA (Expr.eval_const (by omega)) (by omega)) hmem_bp
    set rB := Function.update rA 7 t.batchPtr
    have heBaseB : (Expr.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5))).eval P.w
        ⟨st.mem, rB, st.pos⟩ = some (descPtr + 3 * i) :=
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rB, rA, hr1]))
        (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp [rB, rA, hr5]))
          (by omega)) (by omega)
    have heW : (Expr.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5)))
        (.const 2))).eval P.w ⟨st.mem, rB, st.pos⟩ = some t.W :=
      Expr.eval_load_of_eq (Expr.eval_add heBaseB (Expr.eval_const (by omega)) (by omega)) hmem_W
    set rC := Function.update rB 8 t.W
    have heAddr : (Expr.bin .add (.reg 3) (.reg 5)).eval P.w ⟨st.mem, rC, st.pos⟩ = some (h + i) :=
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr3]))
        (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr5])) (by omega)
    have heVal : (Expr.bin .add (.reg 4) (.reg 8)).eval P.w ⟨st.mem, rC, st.pos⟩ =
        some (st.regs 4 + t.W) :=
      Expr.eval_add (Expr.eval_reg_of_eq (by simp [rC, rB, rA]))
        (Expr.eval_reg_of_eq (by simp [rC])) hhpW_lt
    have heArgs : evalArgs P.w ⟨mem₁, rC, st.pos⟩ [.reg 0, .reg 6, .reg 7, .reg 8, .reg 4] =
        some [spanTbl, t.slot, t.batchPtr, t.W, st.regs 4] :=
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA, hr0])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC])) <|
      evalArgs_cons (Expr.eval_reg_of_eq (by simp [rC, rB, rA])) <| evalArgs_nil _ _
    have hr_call : Runs P.w p ω'
        (.call 4 (bSpan + bsIdxOp0 + 1) [.reg 0, .reg 6, .reg 7, .reg 8, .reg 4])
        ⟨mem₁, rC, st.pos⟩ .normal ⟨st₁.mem, Function.update rC 4 o₁.value, st₁.pos⟩
        (argsSize [.reg 0, .reg 6, .reg 7, .reg 8, .reg 4] + c₁ + 1) :=
      runs_call_iff.mpr ⟨_, bd, o₁, st₁, c₁, heArgs, hbd, hrun₁, rfl, rfl, rfl⟩
    have hr_store : Runs P.w p ω'
        (.store (.bin .add (.reg 3) (.reg 5)) (.bin .add (.reg 4) (.reg 8)))
        ⟨st.mem, rC, st.pos⟩ .normal ⟨mem₁, rC, st.pos⟩
        ((Expr.bin .add (.reg 3) (.reg 5)).size + (Expr.bin .add (.reg 4) (.reg 8)).size + 1) :=
      runs_store_iff.mpr ⟨h + i, st.regs 4 + t.W, heAddr, heVal, rfl, rfl, rfl⟩
    have hr_a8 : Runs P.w p ω'
        (.assign 8 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5))) (.const 2))))
        ⟨st.mem, rB, st.pos⟩ .normal ⟨st.mem, rC, st.pos⟩
        ((Expr.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5))) (.const 2))).size + 1) :=
      runs_assign_iff.mpr ⟨t.W, heW, rfl, rfl, rfl⟩
    have hr_a7 : Runs P.w p ω'
        (.assign 7 (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5))) (.const 1))))
        ⟨st.mem, rA, st.pos⟩ .normal ⟨st.mem, rB, st.pos⟩
        ((Expr.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5))) (.const 1))).size + 1) :=
      runs_assign_iff.mpr ⟨t.batchPtr, heBp, rfl, rfl, rfl⟩
    have hr_a6 : Runs P.w p ω'
        (.assign 6 (.load (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5)))))
        st .normal ⟨st.mem, rA, st.pos⟩
        ((Expr.load (.bin .add (.reg 1) (.bin .mul (.const 3) (.reg 5)))).size + 1) :=
      runs_assign_iff.mpr ⟨t.slot, heSlot, rfl, rfl, rfl⟩
    have hr_all := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a6,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a7,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_a8,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_store, hr_call, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    refine ⟨.normal, _, _, hr_all, ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, x', ?_, ?_⟩, ?_⟩, ?_⟩
    · simp [rC, rB, rA, hr0]
    · simp [rC, rB, rA, hr1]
    · simp [rC, rB, rA, hr2]
    · simp [rC, rB, rA, hr3]
    · simp
    · simp only [Function.update_of_ne (show (4 : ℕ) ≠ 5 by decide), Function.update_self]; omega
    · simp only [Function.update_of_ne (show (4 : ℕ) ≠ 5 by decide), Function.update_self]; omega
    · simp; exact hz'
    · intro a ha hnf
      change st₁.mem a = mem₀ a
      rw [hfr₁ a (by omega) (fun hf => by
        rcases hfooti a hf with hf' | ⟨hle, _⟩
        · exact hnf hf'
        · omega)]
      simp only [mem₁]
      rw [Function.update_of_ne (by omega)]
      exact hfr a ha hnf
    · intro j hj
      change h + tasks.length ≤ st₁.mem (h + j) ∧ st₁.mem (h + j) ≤ o₁.value
      have hnf_hj : ¬ (bucketSpannerRep P cap).foot spanTbl x6i (h + j) := fun hf => by
        rcases hfooti (h + j) hf with hf' | ⟨hle, _⟩
        · have := hfoot (h + j) hf'; omega
        · omega
      rw [hfr₁ (h + j) (by omega) hnf_hj]
      rcases Nat.lt_or_ge j i with hji | hji
      · simp only [mem₁]
        rw [Function.update_of_ne (by omega)]
        have := houts j hji; omega
      · have hj' : j = i := by omega
        subst hj'
        simp only [mem₁, Function.update_self]
        obtain ⟨_, uhOutWords, _, _, _, _, _, _, _, hhdr2, _⟩ := hdsPost.2.1
        have hOut_lt : st.regs 4 + t.W + 2 < o₁.value := by
          by_contra hge
          have hzero := hz' (st.regs 4 + t.W + 2) (by omega)
          simp only [opWords, List.getD, List.getElem?_cons_succ, List.getElem?_cons_zero,
            Option.getD_some] at hhdr2
          omega
        omega
    · intro j hj
      rcases Nat.lt_or_ge j i with hji | hji
      · exact hph j hji
      · have hj' : j = i := by omega
        subst hj'
        rw [hgetD]; omega
    · exact hrep'
    · intro a ha
      simp only [Function.update_of_ne (show (4 : ℕ) ≠ 5 by decide), Function.update_self]
      rcases hft₁ a ha with hf | ⟨hle, hlt⟩
      · rcases hfooti a hf with hf' | ⟨hle', hlt'⟩
        · exact Or.inl hf'
        · exact Or.inr ⟨hle', by omega⟩
      · change st.regs 4 ≤ a at hle
        exact Or.inr ⟨by omega, hlt⟩
    · simp [rC, rB, rA, hr5]
    · unfold spanUpdStepCost
      rw [hgetD]
      simp only [Expr.size, argsSize]
      omega
  -- Chain the whole procedure: `assign 4 (h + n) ;; forRange ;; ret (reg 4)`.
  have hloop := Triple.forRange_le
    (P := fun st => st.mem = mem₀ ∧ st.regs 0 = spanTbl ∧ st.regs 1 = descPtr ∧
      st.regs 2 = tasks.length ∧ st.regs 3 = h ∧ st.regs 4 = h + tasks.length)
    (spanUpdStepCost P S6 mem₀ tasks) 0 tasks.length (Nat.zero_le _)
    hw1 (fun _ => hn_lt)
    (fun st hst => by
      obtain ⟨hmem, hr0, hr1, hr2, hr3, hr4⟩ := hst
      refine ⟨Expr.eval_const (by omega), ?_⟩
      refine ⟨by simp [hr0], by simp [hr1], by simp [hr2], by simp [hr3], by simp,
        by simp [hr4], by simp [hr4], by simp [hr4, hmem]; exact fun a ha => hz a (by omega),
        fun a _ _ => by rw [hmem], fun j hj => absurd hj (Nat.not_lt_zero _),
        fun j hj => absurd hj (Nat.not_lt_zero _), x6, ?_, fun a ha => Or.inl ha⟩
      simpa [hmem, spanUpdAfter] using hrep)
    (fun i st _ _ hInv => hInv.2.2.2.2.1)
    (fun i st _ _ hInv => Expr.eval_reg_of_eq hInv.2.2.1)
    (fun i _ hi => hbody i hi)
  have heInit : (Expr.bin .add (.reg 3) (.reg 2)).eval P.w
      (startState [spanTbl, descPtr, tasks.length, h] mem₀ pos) = some (h + tasks.length) :=
    Expr.eval_add (Expr.eval_reg_of_eq (by simp [startState]))
      (Expr.eval_reg_of_eq (by simp [startState])) hhn_lt
  set stInit := { startState [spanTbl, descPtr, tasks.length, h] mem₀ pos with
    regs := Function.update (startState [spanTbl, descPtr, tasks.length, h] mem₀ pos).regs 4
      (h + tasks.length) }
  have hr_init : Runs P.w p ω (.assign 4 (.bin .add (.reg 3) (.reg 2)))
      (startState [spanTbl, descPtr, tasks.length, h] mem₀ pos) .normal stInit
      ((Expr.bin .add (.reg 3) (.reg 2)).size + 1) :=
    runs_assign_iff.mpr ⟨h + tasks.length, heInit, rfl, rfl, rfl⟩
  obtain ⟨oL, stL, cL, hrunL, hpostL, hcL⟩ := hloop stInit ω
    ⟨rfl, by simp [stInit, startState], by simp [stInit, startState],
     by simp [stInit, startState], by simp [stInit, startState], by simp [stInit]⟩
  cases oL with
  | returned _ => cases hpostL
  | normal =>
  have hInvEnd := hpostL
  obtain ⟨-, -, -, -, -, hloE, hhiE, hzE, hfrE, houtsE, hphE, x', hrepE, hfootE⟩ := hInvEnd
  rw [List.take_length] at hhiE hrepE
  have hr_ret : Runs P.w p ω (.ret (.reg 4)) stL (.returned (stL.regs 4)) stL
      ((Expr.reg 4).size + 1) :=
    runs_ret_iff.mpr ⟨stL.regs 4, Expr.eval_reg_of_eq rfl, rfl, rfl, rfl⟩
  have hr_full : Runs P.w p ω (asmFirstSpanUpdStmt (bSpan + bsIdxOp0 + 1))
      (startState [spanTbl, descPtr, tasks.length, h] mem₀ pos) (.returned (stL.regs 4)) stL
      (((Expr.bin .add (.reg 3) (.reg 2)).size + 1) +
        (cL + ((Expr.reg 4).size + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨stInit, _, _, hr_init,
      runs_seq_iff.mpr (Or.inr ⟨stL, _, _, hrunL, hr_ret, rfl⟩), rfl⟩)
  -- Telescope the amortized cost bound via `sum_tele`.
  have hrc : rangeCost (spanUpdStepCost P S6 mem₀ tasks) 0 tasks.length =
      ((List.range tasks.length).map (spanUpdStepCost P S6 mem₀ tasks)).sum := by
    simp [rangeCost, List.range'_eq_map_range]
  have htele := sum_tele
    (fun j => spanTaskCost P S6 mem₀ (tasks.getD j ⟨0, 0, 0⟩))
    (fun j => specPhi P (spanUpdAfter P S6 mem₀ (tasks.take j)))
    tasks.length hphE
  have hstep_sum : ((List.range tasks.length).map (spanUpdStepCost P S6 mem₀ tasks)).sum =
      80 * tasks.length +
        ((List.range tasks.length).map fun j =>
          spanTaskCost P S6 mem₀ (tasks.getD j ⟨0, 0, 0⟩) +
            specPhi P (spanUpdAfter P S6 mem₀ (tasks.take j)) -
            specPhi P (spanUpdAfter P S6 mem₀ (tasks.take (j + 1)))).sum := by
    have h1 : ∀ (n : ℕ) (f : ℕ → ℕ),
        ((List.range n).map fun j => 80 + f j).sum = 80 * n + ((List.range n).map f).sum := by
      intro n f; induction n with
      | zero => simp
      | succ m ih => simp [List.range_succ, List.sum_append, ih]; omega
    exact h1 _ _
  have hmap_sum : ((List.range tasks.length).map fun j =>
        spanTaskCost P S6 mem₀ (tasks.getD j ⟨0, 0, 0⟩)).sum =
      (tasks.map (spanTaskCost P S6 mem₀)).sum := by
    congr 1
    apply List.ext_getElem (by simp)
    intro j h₁ h₂
    simp only [List.length_map, List.length_range] at h₁
    simp [List.getElem?_eq_getElem h₁]
  have hplus_sum : (tasks.map fun t => spanTaskCost P S6 mem₀ t + 95).sum =
      (tasks.map (spanTaskCost P S6 mem₀)).sum + 95 * tasks.length := by
    have haux : ∀ (l : List SpanUpdTask), (l.map fun t => spanTaskCost P S6 mem₀ t + 95).sum =
        (l.map (spanTaskCost P S6 mem₀)).sum + 95 * l.length := by
      intro l; induction l with
      | nil => simp
      | cons a as ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
    exact haux tasks
  have hphi0 : (bucketSpannerRep P cap).phi spanTbl x6 mem₀ =
      specPhi P (spanUpdAfter P S6 mem₀ (tasks.take 0)) := by
    rw [List.take_zero, spanUpdAfter]; exact bucketPhi_eq_specPhi hrep
  have hphiN : (bucketSpannerRep P cap).phi spanTbl x' stL.mem =
      specPhi P (spanUpdAfter P S6 mem₀ (tasks.take tasks.length)) := by
    rw [List.take_length]; exact bucketPhi_eq_specPhi hrepE
  refine ⟨.returned (stL.regs 4), stL, _, x', hr_full, hrepE, houtsE, hloE, hhiE, hzE, hfrE,
    hfootE, ?_⟩
  simp only [Expr.size] at hcL ⊢
  rw [hrc, hstep_sum] at hcL
  rw [hphi0, hphiN, hplus_sum]
  rw [hmap_sum] at htele
  omega

end

end MinCostFlow.SparseCore.Program
