module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutHelpers

import WordRAM.Tactic

/-!
# Phase 4 workspace and per-slot `D` / `R` / new-slot scanners (`AssemblyFirstStepSlotScanD`)

Defines the fixed `O(eCap)` Phase 4 workspace layout (`p4WsSize eCap = 11 * eCap + 4`,
`Phase4WSAt`), the push into the copy buffer (`p4PushCopy_runs`), and three deterministic,
zero-heap Word-RAM scanners whose writes stay strictly inside `[ws, ws + p4WsSize eCap)`. Their
run lemmas are in `AssemblyFirstStepSlotScanProof.lean`, `AssemblyFirstStepSlotScanR.lean` and
`AssemblyFirstStepSlotScanNew.lean`:
1. `asmFirstScanSlotDStmt fPush fMark` (`[gEPres, hEPres, dPtr, dLen, ws, eCap]`):
   scans `D` of an updated slot, updating `inDtot`, `inAct`, `inTgt`, `delSup`, and `insSup` in
   `≤ 170 * dLen + 60` steps.
2. `asmFirstScanSlotRStmt fPush` (`[gEPres, hEPres, rPtr, rLen, isOld, ws, eCap]`):
   scans `R` of an updated slot, updating `reemb` and (when `isOld ≠ 0 ∧ e ∈ GE \ HE`) pushing `e`
   into the slot's deduplicated `copyBuf` in `≤ 135 * rLen + 65` steps.
3. `asmFirstScanNewSlotStmt fPush` (`[gEList, gM, hEPres, ws, eCap]`):
   scans `G.eList` of a newly active slot, resetting `copyLen := 0`, setting `inAct[e] := 1` and
   `inTgt[e] := hEPres[e]`, pushing `e` into `insSup`, and (when `e ∉ HE`) pushing `e` into
   `copyBuf` in `≤ 135 * gM + 75` steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## Fixed Phase 4 workspace layout (`11 * eCap + 4` words at `ws`) -/

def p4WsSize (eCap : ℕ) : ℕ := 11 * eCap + 4
def p4InDtot (ws : ℕ) : ℕ := ws
def p4InAct (ws eCap : ℕ) : ℕ := ws + eCap
def p4InTgt (ws eCap : ℕ) : ℕ := ws + 2 * eCap
def p4InDelSup (ws eCap : ℕ) : ℕ := ws + 3 * eCap
def p4DelSup (ws eCap : ℕ) : ℕ := ws + 4 * eCap
def p4InInsSup (ws eCap : ℕ) : ℕ := ws + 5 * eCap
def p4InsSup (ws eCap : ℕ) : ℕ := ws + 6 * eCap
def p4InReemb (ws eCap : ℕ) : ℕ := ws + 7 * eCap
def p4Reemb (ws eCap : ℕ) : ℕ := ws + 8 * eCap
def p4SeenCopy (ws eCap : ℕ) : ℕ := ws + 9 * eCap
def p4DelLen (ws eCap : ℕ) : ℕ := ws + 10 * eCap
def p4InsLen (ws eCap : ℕ) : ℕ := ws + 10 * eCap + 1
def p4ReembLen (ws eCap : ℕ) : ℕ := ws + 10 * eCap + 2
def p4CopyLen (ws eCap : ℕ) : ℕ := ws + 10 * eCap + 3
def p4CopyBuf (ws eCap : ℕ) : ℕ := ws + 10 * eCap + 4

/-- The places of the workspace as equations, so that `omega` can use them as hypotheses. -/
theorem p4_layout (ws eCap : ℕ) :
    p4WsSize eCap = 11 * eCap + 4 ∧ p4InDtot ws = ws ∧ p4InAct ws eCap = ws + eCap ∧
    p4InTgt ws eCap = ws + 2 * eCap ∧ p4InDelSup ws eCap = ws + 3 * eCap ∧
    p4DelSup ws eCap = ws + 4 * eCap ∧ p4InInsSup ws eCap = ws + 5 * eCap ∧
    p4InsSup ws eCap = ws + 6 * eCap ∧ p4InReemb ws eCap = ws + 7 * eCap ∧
    p4Reemb ws eCap = ws + 8 * eCap ∧ p4SeenCopy ws eCap = ws + 9 * eCap ∧
    p4DelLen ws eCap = ws + 10 * eCap ∧ p4InsLen ws eCap = ws + 10 * eCap + 1 ∧
    p4ReembLen ws eCap = ws + 10 * eCap + 2 ∧ p4CopyLen ws eCap = ws + 10 * eCap + 3 ∧
    p4CopyBuf ws eCap = ws + 10 * eCap + 4 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Abstract state of the fixed Phase 4 workspace `[ws, ws + p4WsSize eCap)`. -/
structure Phase4WS where
  inDtot : Finset ℕ
  inAct : Finset ℕ
  inTgt : Finset ℕ
  delSup : List ℕ
  insSup : List ℕ
  reemb : List ℕ
  seenCopy : Finset ℕ
  copyBuf : List ℕ

/-- In-memory representation of `S : Phase4WS` at `[ws, ws + p4WsSize eCap)`.
Note: `seenCopy` is persistent across slots (never cleared between slots), while `copyBuf` holds the
current slot's deduplicated edge list (`copyBuf.toFinset ⊆ seenCopy` and `copyBuf.Nodup`). -/
def Phase4WSAt (mem : ℕ → ℕ) (ws eCap : ℕ) (S : Phase4WS) : Prop :=
  (∀ e < eCap, mem (p4InDtot ws + e) = if e ∈ S.inDtot then 1 else 0) ∧
  (∀ e < eCap, mem (p4InAct ws eCap + e) = if e ∈ S.inAct then 1 else 0) ∧
  (∀ e < eCap, mem (p4InTgt ws eCap + e) = if e ∈ S.inTgt then 1 else 0) ∧
  DedupBufAt mem (p4InDelSup ws eCap) (p4DelSup ws eCap) (p4DelLen ws eCap) eCap S.delSup ∧
  DedupBufAt mem (p4InInsSup ws eCap) (p4InsSup ws eCap) (p4InsLen ws eCap) eCap S.insSup ∧
  DedupBufAt mem (p4InReemb ws eCap) (p4Reemb ws eCap) (p4ReembLen ws eCap) eCap S.reemb ∧
  (∀ e < eCap, mem (p4SeenCopy ws eCap + e) = if e ∈ S.seenCopy then 1 else 0) ∧
  S.copyBuf.Nodup ∧ (∀ e ∈ S.copyBuf, e < eCap ∧ e ∈ S.seenCopy) ∧
  mem (p4CopyLen ws eCap) = S.copyBuf.length ∧
  ListAt mem (p4CopyBuf ws eCap) S.copyBuf

/-- Pure copy-buffer push (guarded by `seenCopy`). -/
def pushCopy (S : Phase4WS) (e : ℕ) : Phase4WS :=
  if e ∈ S.seenCopy then S
  else { S with seenCopy := insert e S.seenCopy, copyBuf := S.copyBuf ++ [e] }

/-- **Per-slot `D` scanner**, `[gEPres, hEPres, dPtr, dLen, ws, eCap]`. -/
def asmFirstScanSlotDStmt (fPush fMark : ℕ) : Stmt :=
  .assign 6 (.bin .add (.reg 4) (.reg 5)) ;;                              -- inAct
  .assign 7 (.bin .add (.reg 6) (.reg 5)) ;;                              -- inTgt
  .assign 8 (.bin .add (.reg 7) (.reg 5)) ;;                              -- inDelSup
  .assign 9 (.bin .add (.reg 8) (.reg 5)) ;;                              -- delSup
  .assign 10 (.bin .add (.reg 9) (.reg 5)) ;;                             -- inInsSup
  .assign 11 (.bin .add (.reg 10) (.reg 5)) ;;                            -- insSup
  .assign 12 (.bin .add (.reg 4) (.bin .mul (.const 10) (.reg 5))) ;;     -- delLen
  .assign 13 (.bin .add (.reg 12) (.const 1)) ;;                          -- insLen
  forRange 14 (.const 0) (.reg 3)
    (.assign 15 (.load (.bin .add (.reg 2) (.reg 14))) ;;
     .store (.bin .add (.reg 4) (.reg 15)) (.const 1) ;;
     .call 16 fMark [.reg 0, .reg 1, .reg 6, .reg 7, .reg 15] ;;
     .call 16 fPush [.reg 8, .reg 9, .reg 12, .reg 15] ;;
     .call 16 fPush [.reg 10, .reg 11, .reg 13, .reg 15]) ;;
  .ret (.const 0)

/-- **Per-slot `R` scanner**, `[gEPres, hEPres, rPtr, rLen, isOld, ws, eCap]`. -/
def asmFirstScanSlotRStmt (fPush : ℕ) : Stmt :=
  .assign 7 (.bin .add (.reg 5) (.bin .mul (.const 7) (.reg 6))) ;;       -- inReemb
  .assign 8 (.bin .add (.reg 7) (.reg 6)) ;;                              -- reemb
  .assign 9 (.bin .add (.reg 8) (.reg 6)) ;;                              -- seenCopy
  .assign 10 (.bin .add (.bin .add (.reg 5) (.bin .mul (.const 10) (.reg 6))) (.const 2)) ;; -- reembLen
  .assign 11 (.bin .add (.reg 10) (.const 1)) ;;                          -- copyLen
  .assign 12 (.bin .add (.reg 11) (.const 1)) ;;                          -- copyBuf
  forRange 13 (.const 0) (.reg 3)
    (.assign 14 (.load (.bin .add (.reg 2) (.reg 13))) ;;
     .call 15 fPush [.reg 7, .reg 8, .reg 10, .reg 14] ;;
     .cond (.reg 4)
       (.cond (.load (.bin .add (.reg 0) (.reg 14)))
         (.cond (.bin .eq (.load (.bin .add (.reg 1) (.reg 14))) (.const 0))
           (.cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 14))) (.const 0))
             (.store (.bin .add (.reg 9) (.reg 14)) (.const 1) ;;
              .assign 16 (.load (.reg 11)) ;;
              .store (.bin .add (.reg 12) (.reg 16)) (.reg 14) ;;
              .store (.reg 11) (.bin .add (.reg 16) (.const 1)))
             .nop)
           .nop)
         .nop)
       .nop) ;;
  .ret (.const 0)

/-- **Per-newly-active-slot `G.eList` scanner**, `[gEList, gM, hEPres, ws, eCap]`. -/
def asmFirstScanNewSlotStmt (fPush : ℕ) : Stmt :=
  .assign 5 (.bin .add (.reg 3) (.reg 4)) ;;                              -- inAct
  .assign 6 (.bin .add (.reg 5) (.reg 4)) ;;                              -- inTgt
  .assign 7 (.bin .add (.reg 3) (.bin .mul (.const 5) (.reg 4))) ;;       -- inInsSup
  .assign 8 (.bin .add (.reg 7) (.reg 4)) ;;                              -- insSup
  .assign 9 (.bin .add (.reg 3) (.bin .mul (.const 9) (.reg 4))) ;;       -- seenCopy
  .assign 10 (.bin .add (.bin .add (.reg 3) (.bin .mul (.const 10) (.reg 4))) (.const 1)) ;; -- insLen
  .assign 11 (.bin .add (.reg 10) (.const 2)) ;;                          -- copyLen
  .assign 12 (.bin .add (.reg 11) (.const 1)) ;;                          -- copyBuf
  .store (.reg 11) (.const 0) ;;
  forRange 13 (.const 0) (.reg 1)
    (.assign 14 (.load (.bin .add (.reg 0) (.reg 13))) ;;
     .store (.bin .add (.reg 5) (.reg 14)) (.const 1) ;;
     .assign 15 (.load (.bin .add (.reg 2) (.reg 14))) ;;
     .store (.bin .add (.reg 6) (.reg 14)) (.reg 15) ;;
     .call 16 fPush [.reg 7, .reg 8, .reg 10, .reg 14] ;;
     .cond (.bin .eq (.reg 15) (.const 0))
       (.cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 14))) (.const 0))
         (.store (.bin .add (.reg 9) (.reg 14)) (.const 1) ;;
          .assign 16 (.load (.reg 11)) ;;
          .store (.bin .add (.reg 12) (.reg 16)) (.reg 14) ;;
          .store (.reg 11) (.bin .add (.reg 16) (.const 1)))
         .nop)
       .nop) ;;
  .ret (.const 0)

end

public section

theorem asmFirstScanSlotDStmt_noRand (fPush fMark : ℕ) : (asmFirstScanSlotDStmt fPush fMark).NoRand := by
  simp [asmFirstScanSlotDStmt, forRange, forUp, Stmt.NoRand]

theorem asmFirstScanSlotRStmt_noRand (fPush : ℕ) : (asmFirstScanSlotRStmt fPush).NoRand := by
  simp [asmFirstScanSlotRStmt, forRange, forUp, Stmt.NoRand]

theorem asmFirstScanNewSlotStmt_noRand (fPush : ℕ) : (asmFirstScanNewSlotStmt fPush).NoRand := by
  simp [asmFirstScanNewSlotStmt, forRange, forUp, Stmt.NoRand]

/-- `dedupBufAt_of_agree` with the agreement asked on all `eCap` cells of the buffer. -/
lemma dedupBufAt_of_agree_cap {mem₁ mem₂ : ℕ → ℕ} {flagPtr bufPtr lenAddr eCap : ℕ} {L : List ℕ}
    (h : DedupBufAt mem₁ flagPtr bufPtr lenAddr eCap L)
    (hfl : ∀ e < eCap, mem₂ (flagPtr + e) = mem₁ (flagPtr + e))
    (hbuf : ∀ i < eCap, mem₂ (bufPtr + i) = mem₁ (bufPtr + i))
    (hlen : mem₂ lenAddr = mem₁ lenAddr) :
    DedupBufAt mem₂ flagPtr bufPtr lenAddr eCap L :=
  dedupBufAt_of_agree h hfl (fun i hi => hbuf i (lt_of_lt_of_le hi (dedupBuf_length_le h))) hlen

lemma phase4WSAt_zero {mem : ℕ → ℕ} {ws eCap : ℕ} (hz : ZeroFrom mem ws) :
    Phase4WSAt mem ws eCap ⟨∅, ∅, ∅, [], [], [], ∅, []⟩ := by
  refine ⟨fun e _ => by simp [p4InDtot, hz (ws + e) (by omega)],
    fun e _ => by simp [p4InAct, hz (ws + eCap + e) (by omega)],
    fun e _ => by simp [p4InTgt, hz (ws + 2 * eCap + e) (by omega)],
    dedupBufAt_zero (fun e _ => hz _ (by simp [p4InDelSup]; omega)) (hz _ (by simp [p4DelLen])),
    dedupBufAt_zero (fun e _ => hz _ (by simp [p4InInsSup]; omega)) (hz _ (by simp [p4InsLen]; omega)),
    dedupBufAt_zero (fun e _ => hz _ (by simp [p4InReemb]; omega)) (hz _ (by simp [p4ReembLen]; omega)),
    fun e _ => by simp only [Finset.notMem_empty, ↓reduceIte]; exact hz _ (by simp [p4SeenCopy]; omega),
    List.nodup_nil, fun _ h => (by cases h), hz _ (by simp [p4CopyLen]; omega), fun _ h => (by cases h)⟩

lemma phase4WSAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {ws eCap : ℕ} {S : Phase4WS}
    (h : Phase4WSAt mem₁ ws eCap S)
    (hag : ∀ a, ws ≤ a → a < ws + p4WsSize eCap → mem₂ a = mem₁ a) :
    Phase4WSAt mem₂ ws eCap S := by
  obtain ⟨hD, hA, hT, hDS, hIS, hR, hSC, hnd, hcb, hcl, hclat⟩ := h
  have hcb_le : S.copyBuf.length ≤ eCap := by
    rw [← List.toFinset_card_of_nodup hnd]
    calc S.copyBuf.toFinset.card ≤ (Finset.range eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (hcb e (List.mem_toFinset.mp he)).1
      _ = eCap := Finset.card_range eCap
  refine ⟨fun e he => (hag _ (by simp [p4InDtot]) (by simp [p4InDtot, p4WsSize]; omega)).trans (hD e he),
    fun e he => (hag _ (by simp [p4InAct]; omega) (by simp [p4InAct, p4WsSize]; omega)).trans (hA e he),
    fun e he => (hag _ (by simp [p4InTgt]; omega) (by simp [p4InTgt, p4WsSize]; omega)).trans (hT e he),
    dedupBufAt_of_agree hDS
      (fun e he => hag _ (by simp [p4InDelSup]; omega) (by simp [p4InDelSup, p4WsSize]; omega))
      (fun i hi => have := dedupBuf_length_le hDS; hag _ (by simp [p4DelSup]; omega) (by simp [p4DelSup, p4WsSize]; omega))
      (hag _ (by simp [p4DelLen]) (by simp [p4DelLen, p4WsSize]; omega)),
    dedupBufAt_of_agree hIS
      (fun e he => hag _ (by simp [p4InInsSup]; omega) (by simp [p4InInsSup, p4WsSize]; omega))
      (fun i hi => have := dedupBuf_length_le hIS; hag _ (by simp [p4InsSup]; omega) (by simp [p4InsSup, p4WsSize]; omega))
      (hag _ (by simp [p4InsLen]; omega) (by simp [p4InsLen, p4WsSize]; omega)),
    dedupBufAt_of_agree hR
      (fun e he => hag _ (by simp [p4InReemb]; omega) (by simp [p4InReemb, p4WsSize]; omega))
      (fun i hi => have := dedupBuf_length_le hR; hag _ (by simp [p4Reemb]; omega) (by simp [p4Reemb, p4WsSize]; omega))
      (hag _ (by simp [p4ReembLen]; omega) (by simp [p4ReembLen, p4WsSize]; omega)),
    fun e he => (hag _ (by simp [p4SeenCopy]; omega) (by simp [p4SeenCopy, p4WsSize]; omega)).trans (hSC e he),
    hnd, hcb,
    (hag _ (by simp [p4CopyLen]; omega) (by simp [p4CopyLen, p4WsSize]; omega)).trans hcl,
    fun i hi => (hag _ (by simp [p4CopyBuf]; omega) (by simp [p4CopyBuf, p4WsSize]; omega)).trans (hclat i hi)⟩

/-- Helper lemma for the 4-statement `pushCopy` block (regs `9 = seenCopy`, `11 = copyLen`,
`12 = copyBuf`, `14 = e`, `16` scratch). -/
lemma p4PushCopy_runs {w ws eCap e : ℕ} {p : Program} {S : Phase4WS} {st : State} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w) (hws_w : ws + p4WsSize eCap < 2 ^ w) (he : e < eCap)
    (hr9 : st.regs 9 = p4SeenCopy ws eCap) (hr11 : st.regs 11 = p4CopyLen ws eCap)
    (hr12 : st.regs 12 = p4CopyBuf ws eCap) (hr14 : st.regs 14 = e)
    (hW : Phase4WSAt st.mem ws eCap S) :
    ∃ st' c,
      Runs w p ω
        (.cond (.bin .eq (.load (.bin .add (.reg 9) (.reg 14))) (.const 0))
          (.store (.bin .add (.reg 9) (.reg 14)) (.const 1) ;;
           .assign 16 (.load (.reg 11)) ;;
           .store (.bin .add (.reg 12) (.reg 16)) (.reg 14) ;;
           .store (.reg 11) (.bin .add (.reg 16) (.const 1)))
          .nop)
        st .normal st' c ∧
      (∀ r, r ≠ 16 → st'.regs r = st.regs r) ∧
      Phase4WSAt st'.mem ws eCap (pushCopy S e) ∧
      (∀ a, a < ws ∨ ws + p4WsSize eCap ≤ a → st'.mem a = st.mem a) ∧
      (∀ a, ws ≤ a → a < p4SeenCopy ws eCap → st'.mem a = st.mem a) ∧
      (∀ a, p4DelLen ws eCap ≤ a → a < p4CopyLen ws eCap → st'.mem a = st.mem a) ∧
      c ≤ 30 := by
  have h0w : 0 < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by omega
  obtain ⟨hD, hA, hT, hDS, hIS, hR, hSC, hnd, hcb, hcl, hclat⟩ := hW
  have hseen := hSC e he
  have hcb_lt_of_nm : e ∉ S.seenCopy → S.copyBuf.length < eCap := fun hnm => by
    have hnd' : (e :: S.copyBuf).Nodup := List.nodup_cons.mpr ⟨fun hm => hnm (hcb e hm).2, hnd⟩
    have hcard : (e :: S.copyBuf).length ≤ eCap := by
      rw [← List.toFinset_card_of_nodup hnd']
      calc (e :: S.copyBuf).toFinset.card ≤ (Finset.range eCap).card :=
            Finset.card_le_card fun x hx => by
              rcases List.mem_cons.mp (List.mem_toFinset.mp hx) with rfl | hxl
              · exact Finset.mem_range.mpr he
              · exact Finset.mem_range.mpr (hcb x hxl).1
        _ = eCap := Finset.card_range eCap
    simp only [List.length_cons] at hcard; omega
  have hcond_e : (Expr.bin .eq (.load (.bin .add (.reg 9) (.reg 14))) (.const 0)).eval w st =
      some (if e ∈ S.seenCopy then 0 else 1) := by
    have hl : (Expr.load (.bin .add (.reg 9) (.reg 14))).eval w st =
        some (if e ∈ S.seenCopy then 1 else 0) :=
      Expr.eval_load_of_eq
        (Expr.eval_add (Expr.eval_reg_of_eq hr9) (Expr.eval_reg_of_eq hr14) (by simp [p4SeenCopy, p4WsSize] at *; omega))
        hseen
    have := Expr.eval_eq_op hl (Expr.eval_const (st := st) h0w) h1w
    by_cases hm : e ∈ S.seenCopy <;> simpa [hm] using this
  by_cases hm : e ∈ S.seenCopy
  · refine ⟨st, _, runs_cond_iff.mpr ⟨0, 1, by simpa [hm] using hcond_e,
      by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩, fun _ _ => rfl,
      by simpa [pushCopy, hm] using ⟨hD, hA, hT, hDS, hIS, hR, hSC, hnd, hcb, hcl, hclat⟩,
      fun _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, by simp [Expr.size]⟩
  · have hlt := hcb_lt_of_nm hm
    set m1 := Function.update st.mem (p4SeenCopy ws eCap + e) 1
    set r1 := Function.update st.regs 16 S.copyBuf.length
    set m2 := Function.update m1 (p4CopyBuf ws eCap + S.copyBuf.length) e
    set m3 := Function.update m2 (p4CopyLen ws eCap) (S.copyBuf.length + 1)
    have hs1 : Runs w p ω (.store (.bin .add (.reg 9) (.reg 14)) (.const 1)) st .normal ⟨m1, st.regs, st.pos⟩ 5 :=
      runs_store_iff.mpr ⟨p4SeenCopy ws eCap + e, 1,
        Expr.eval_add (Expr.eval_reg_of_eq hr9) (Expr.eval_reg_of_eq hr14) (by simp [p4SeenCopy, p4WsSize] at *; omega),
        Expr.eval_const h1w, rfl, rfl, rfl⟩
    have hm1_cl : m1 (p4CopyLen ws eCap) = S.copyBuf.length := by
      dsimp only [m1]; rw [Function.update_of_ne (by simp [p4SeenCopy, p4CopyLen]; omega)]; exact hcl
    have ha16 : Runs w p ω (.assign 16 (.load (.reg 11))) ⟨m1, st.regs, st.pos⟩ .normal ⟨m1, r1, st.pos⟩ 3 :=
      runs_assign_iff.mpr ⟨S.copyBuf.length, Expr.eval_load_of_eq (Expr.eval_reg_of_eq hr11) hm1_cl, rfl, rfl, rfl⟩
    have hs2 : Runs w p ω (.store (.bin .add (.reg 12) (.reg 16)) (.reg 14))
        ⟨m1, r1, st.pos⟩ .normal ⟨m2, r1, st.pos⟩ 5 :=
      runs_store_iff.mpr ⟨p4CopyBuf ws eCap + S.copyBuf.length, e,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, hr12])) (Expr.eval_reg_of_eq (by simp [r1]))
          (by simp [p4CopyBuf, p4WsSize] at *; omega),
        Expr.eval_reg_of_eq (by simp [r1, hr14]), rfl, rfl, rfl⟩
    have hs3 : Runs w p ω (.store (.reg 11) (.bin .add (.reg 16) (.const 1)))
        ⟨m2, r1, st.pos⟩ .normal ⟨m3, r1, st.pos⟩ 5 :=
      runs_store_iff.mpr ⟨p4CopyLen ws eCap, S.copyBuf.length + 1,
        Expr.eval_reg_of_eq (by simp [r1, hr11]),
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1])) (Expr.eval_const h1w) (by simp [p4WsSize] at *; omega),
        rfl, rfl, rfl⟩
    have hfr_m3 : ∀ a, a ≠ p4SeenCopy ws eCap + e → a ≠ p4CopyBuf ws eCap + S.copyBuf.length →
        a ≠ p4CopyLen ws eCap → m3 a = st.mem a := fun a h1 h2 h3 => by simp [m3, m2, m1, h1, h2, h3]
    refine ⟨⟨m3, r1, st.pos⟩, _,
      runs_cond_iff.mpr ⟨1, _, by simpa [hm] using hcond_e, by
        simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha16,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs2, hs3, rfl⟩), rfl⟩), rfl⟩), rfl⟩,
      fun r hr => by simp [r1, hr], ?_,
      fun a ha => hfr_m3 a (by simp [p4SeenCopy, p4WsSize] at ha ⊢; rcases ha with h | h <;> omega)
        (by simp [p4CopyBuf, p4WsSize] at ha ⊢; rcases ha with h | h <;> omega)
        (by simp [p4CopyLen, p4WsSize] at ha ⊢; rcases ha with h | h <;> omega),
      fun a h1 h2 => hfr_m3 a (by simp [p4SeenCopy] at h2 ⊢; omega)
        (by simp [p4SeenCopy, p4CopyBuf] at h2 ⊢; omega) (by simp [p4SeenCopy, p4CopyLen] at h2 ⊢; omega),
      fun a h1 h2 => hfr_m3 a (by simp [p4DelLen, p4SeenCopy] at h1 ⊢; omega)
        (by simp [p4CopyLen, p4CopyBuf] at h2 ⊢; omega) (by omega),
      by simp [Expr.size]⟩
    simp only [pushCopy, hm, ↓reduceIte]
    refine ⟨fun e' he' => (hfr_m3 _ (by simp [p4InDtot, p4SeenCopy]; omega) (by simp [p4InDtot, p4CopyBuf]; omega)
        (by simp [p4InDtot, p4CopyLen]; omega)).trans (hD e' he'),
      fun e' he' => (hfr_m3 _ (by simp [p4InAct, p4SeenCopy]; omega) (by simp [p4InAct, p4CopyBuf]; omega)
        (by simp [p4InAct, p4CopyLen]; omega)).trans (hA e' he'),
      fun e' he' => (hfr_m3 _ (by simp [p4InTgt, p4SeenCopy]; omega) (by simp [p4InTgt, p4CopyBuf]; omega)
        (by simp [p4InTgt, p4CopyLen]; omega)).trans (hT e' he'),
      dedupBufAt_of_agree hDS
        (fun e' he' => hfr_m3 _ (by simp [p4InDelSup, p4SeenCopy]; omega) (by simp [p4InDelSup, p4CopyBuf]; omega) (by simp [p4InDelSup, p4CopyLen]; omega))
        (fun i hi => by
          change i < S.delSup.length at hi
          have := dedupBuf_length_le hDS
          exact hfr_m3 _ (by simp [p4DelSup, p4SeenCopy]; omega) (by simp [p4DelSup, p4CopyBuf]; omega) (by simp [p4DelSup, p4CopyLen]; omega))
        (hfr_m3 _ (by simp [p4DelLen, p4SeenCopy]; omega) (by simp [p4DelLen, p4CopyBuf]; omega) (by simp [p4DelLen, p4CopyLen])),
      dedupBufAt_of_agree hIS
        (fun e' he' => hfr_m3 _ (by simp [p4InInsSup, p4SeenCopy]; omega) (by simp [p4InInsSup, p4CopyBuf]; omega) (by simp [p4InInsSup, p4CopyLen]; omega))
        (fun i hi => by
          change i < S.insSup.length at hi
          have := dedupBuf_length_le hIS
          exact hfr_m3 _ (by simp [p4InsSup, p4SeenCopy]; omega) (by simp [p4InsSup, p4CopyBuf]; omega) (by simp [p4InsSup, p4CopyLen]; omega))
        (hfr_m3 _ (by simp [p4InsLen, p4SeenCopy]; omega) (by simp [p4InsLen, p4CopyBuf]; omega) (by simp [p4InsLen, p4CopyLen])),
      dedupBufAt_of_agree hR
        (fun e' he' => hfr_m3 _ (by simp [p4InReemb, p4SeenCopy]; omega) (by simp [p4InReemb, p4CopyBuf]; omega) (by simp [p4InReemb, p4CopyLen]; omega))
        (fun i hi => by
          change i < S.reemb.length at hi
          have := dedupBuf_length_le hR
          exact hfr_m3 _ (by simp [p4Reemb, p4SeenCopy]; omega) (by simp [p4Reemb, p4CopyBuf]; omega) (by simp [p4Reemb, p4CopyLen]; omega))
        (hfr_m3 _ (by simp [p4ReembLen, p4SeenCopy]; omega) (by simp [p4ReembLen, p4CopyBuf]; omega) (by simp [p4ReembLen, p4CopyLen])),
      fun e' he' => by
        dsimp only [m3, m2]
        rw [Function.update_of_ne (by simp [p4SeenCopy, p4CopyLen]; omega),
          Function.update_of_ne (by simp [p4SeenCopy, p4CopyBuf]; omega)]
        by_cases hee : e' = e
        · subst hee; simp [m1]
        · simp only [m1, Function.update_of_ne (by omega : p4SeenCopy ws eCap + e' ≠ p4SeenCopy ws eCap + e),
            Finset.mem_insert, hee, false_or]; exact hSC e' he',
      List.nodup_append.mpr ⟨hnd, List.nodup_singleton e, fun x hx y hy hxy =>
        hm (by rw [← List.mem_singleton.mp hy, ← hxy]; exact (hcb x hx).2)⟩,
      fun x hx => by
        rcases List.mem_append.mp hx with h1 | h2
        · exact ⟨(hcb x h1).1, Finset.mem_insert_of_mem (hcb x h1).2⟩
        · rw [List.mem_singleton.mp h2]; exact ⟨he, Finset.mem_insert_self e _⟩,
      by simp [m3],
      fun i hi => by
        simp only [List.length_append, List.length_singleton] at hi
        dsimp only [m3]; rw [Function.update_of_ne (by simp [p4CopyBuf, p4CopyLen]; omega)]
        by_cases hil : i < S.copyBuf.length
        · rw [List.getElem_append_left hil]
          dsimp only [m2, m1]
          rw [Function.update_of_ne (by omega : p4CopyBuf ws eCap + i ≠ p4CopyBuf ws eCap + S.copyBuf.length),
            Function.update_of_ne (by simp [p4CopyBuf, p4SeenCopy]; omega)]
          exact hclat i hil
        · have hieq : i = S.copyBuf.length := by omega
          subst hieq; rw [List.getElem_append_right le_rfl]; simp [m2]⟩

end

end MinCostFlow.SparseCore.Program
