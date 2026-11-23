module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutFlags

import WordRAM.Tactic

/-!
# Phase 4 deduplicated-buffer and slot-marking helpers (`AssemblyFirstStepOutHelpers`)

Provides four tiny, deterministic, zero-heap Word-RAM building blocks reused throughout Phase 4:
1. `asmFirstPushDedupStmt` (`[flagPtr, bufPtr, lenAddr, e]`): `O(1)` deduplicated append maintaining
   `DedupBufAt mem flagPtr bufPtr lenAddr eCap L` (`L.Nodup`, `L.length ≤ eCap`, `ListAt`, exact
   membership flags).
2. `asmFirstMarkSlotEdgeStmt` (`[gEPres, hEPres, inActPtr, inTgtPtr, e]`): `O(1)` update of
   `inAct[e]` / `inTgt[e]` from a slot's `G` and `H` presence arrays.
3. `asmFirstAppendListStmt fPush` (`[flagPtr, bufPtr, lenAddr, srcPtr, srcLen]`): appends an array
   `srcPtr[0..srcLen)` into a `DedupBufAt` in `≤ 55 * srcLen + 20` steps.
4. `asmFirstSeedBatchStmt fPush` (`[batch, inDelSup, delSup, delLenAddr, inInsSup, insSup,
   insLenAddr]`): seeds `delSup` with `batchDeletes U` and `insSup` with `batchDeletes U ∪ insU`
   in `≤ 120 * U.length + 20` steps.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.SparseCore MinCostFlow.DynSpanner.Program

@[expose] public section

/-- A deduplicated edge buffer backed by an `eCap`-word presence array `flagPtr`, an `eCap`-word
element array `bufPtr`, and a single length word `lenAddr`. -/
def DedupBufAt (mem : ℕ → ℕ) (flagPtr bufPtr lenAddr eCap : ℕ) (L : List ℕ) : Prop :=
  L.Nodup ∧
  (∀ e ∈ L, e < eCap) ∧
  mem lenAddr = L.length ∧
  ListAt mem bufPtr L ∧
  ∀ e < eCap, mem (flagPtr + e) = if e ∈ L then 1 else 0

/-- Pure deduplicated push of one element `e` onto `L`. -/
def pushDedup (L : List ℕ) (e : ℕ) : List ℕ :=
  if e ∈ L then L else L ++ [e]

/-- Pure deduplicated append of a list `src` onto `L`. -/
def appendDedup (L src : List ℕ) : List ℕ :=
  src.foldl pushDedup L

/-- **Deduplicated push**, `[flagPtr, bufPtr, lenAddr, e]`: if `mem[flagPtr + e] = 0`, sets
`mem[flagPtr + e] := 1`, writes `e` at `bufPtr + mem[lenAddr]`, and increments `mem[lenAddr]`. -/
def asmFirstPushDedupStmt : Stmt :=
  .assign 4 (.load (.bin .add (.reg 0) (.reg 3))) ;;
  .cond (.bin .eq (.reg 4) (.const 0))
    (.store (.bin .add (.reg 0) (.reg 3)) (.const 1) ;;
     .assign 5 (.load (.reg 2)) ;;
     .store (.bin .add (.reg 1) (.reg 5)) (.reg 3) ;;
     .store (.reg 2) (.bin .add (.reg 5) (.const 1)))
    .nop ;;
  .ret (.const 0)

/-- **Slot-edge active/target marker**, `[gEPres, hEPres, inActPtr, inTgtPtr, e]`: if
`mem[gEPres + e] ≠ 0`, sets `mem[inActPtr + e] := 1` and `mem[inTgtPtr + e] := mem[hEPres + e]`. -/
def asmFirstMarkSlotEdgeStmt : Stmt :=
  .assign 5 (.load (.bin .add (.reg 0) (.reg 4))) ;;
  .cond (.reg 5)
    (.store (.bin .add (.reg 2) (.reg 4)) (.const 1) ;;
     .store (.bin .add (.reg 3) (.reg 4)) (.load (.bin .add (.reg 1) (.reg 4))))
    .nop ;;
  .ret (.const 0)

/-- **Deduplicated array append**, `[flagPtr, bufPtr, lenAddr, srcPtr, srcLen]`. -/
def asmFirstAppendListStmt (fPush : ℕ) : Stmt :=
  forRange 5 (.const 0) (.reg 4)
    (.assign 6 (.load (.bin .add (.reg 3) (.reg 5))) ;;
     .call 7 fPush [.reg 0, .reg 1, .reg 2, .reg 6]) ;;
  .ret (.const 0)

/-- Loop body for `asmFirstSeedBatchStmt`:
regs `0 = batch`, `1..3 = delSup (flag, buf, lenAddr)`, `4..6 = insSup (flag, buf, lenAddr)`,
`7 = nU`, `8 = cur`, `9 = i`, `10..13` scratch. -/
def asmFirstSeedBatchBody (fPush : ℕ) : Stmt :=
  .assign 10 (.load (.reg 8)) ;;
  .cond (.bin .eq (.reg 10) (.const 0))
    (.assign 11 (.load (.bin .add (.reg 8) (.const 1))) ;;
     .call 13 fPush [.reg 4, .reg 5, .reg 6, .reg 11] ;;
     .assign 8 (.bin .add (.reg 8) (.const 4)))
    (.cond (.bin .eq (.reg 10) (.const 1))
      (.assign 11 (.load (.bin .add (.reg 8) (.const 1))) ;;
       .call 13 fPush [.reg 1, .reg 2, .reg 3, .reg 11] ;;
       .call 13 fPush [.reg 4, .reg 5, .reg 6, .reg 11] ;;
       .assign 8 (.bin .add (.reg 8) (.const 2)))
      (.assign 11 (.load (.bin .add (.reg 8) (.const 3))) ;;
       .assign 12 (.load (.bin .add (.reg 8) (.const 4))) ;;
       .assign 8 (.bin .add (.bin .add (.bin .add (.reg 8) (.const 5)) (.reg 11)) (.reg 12))))

/-- **Seed `delSup` and `insSup` from input batch `U`**,
`[batch, inDelSup, delSup, delLenAddr, inInsSup, insSup, insLenAddr]`. -/
def asmFirstSeedBatchStmt (fPush : ℕ) : Stmt :=
  .assign 7 (.load (.reg 0)) ;;
  .assign 8 (.bin .add (.reg 0) (.const 1)) ;;
  forRange 9 (.const 0) (.reg 7) (asmFirstSeedBatchBody fPush) ;;
  .ret (.const 0)

/-- Edges inserted by `U`. -/
def batchInsEdges (U : List Update) : Finset ℕ :=
  (U.filterMap fun | .insert e _ _ => some e | _ => none).toFinset

end

public section

theorem asmFirstPushDedupStmt_noRand : asmFirstPushDedupStmt.NoRand := by
  simp [asmFirstPushDedupStmt, Stmt.NoRand]

theorem asmFirstMarkSlotEdgeStmt_noRand : asmFirstMarkSlotEdgeStmt.NoRand := by
  simp [asmFirstMarkSlotEdgeStmt, Stmt.NoRand]

theorem asmFirstAppendListStmt_noRand (fPush : ℕ) : (asmFirstAppendListStmt fPush).NoRand := by
  simp [asmFirstAppendListStmt, forRange, forUp, Stmt.NoRand]

theorem asmFirstSeedBatchStmt_noRand (fPush : ℕ) : (asmFirstSeedBatchStmt fPush).NoRand := by
  simp [asmFirstSeedBatchStmt, asmFirstSeedBatchBody, forRange, forUp, Stmt.NoRand]

/-! ## Pure properties of `DedupBufAt`, `pushDedup`, `appendDedup` -/

lemma dedupBuf_length_le {mem : ℕ → ℕ} {flagPtr bufPtr lenAddr eCap : ℕ} {L : List ℕ}
    (h : DedupBufAt mem flagPtr bufPtr lenAddr eCap L) : L.length ≤ eCap := by
  have h1 : L.toFinset.card = L.length := List.toFinset_card_of_nodup h.1
  have h2 : L.toFinset ⊆ Finset.range eCap := fun e he =>
    Finset.mem_range.mpr (h.2.1 e (List.mem_toFinset.mp he))
  calc L.length = L.toFinset.card := h1.symm
    _ ≤ (Finset.range eCap).card := Finset.card_le_card h2
    _ = eCap := Finset.card_range eCap

lemma dedupBuf_length_lt_of_not_mem {mem : ℕ → ℕ} {flagPtr bufPtr lenAddr eCap e : ℕ} {L : List ℕ}
    (h : DedupBufAt mem flagPtr bufPtr lenAddr eCap L) (he : e < eCap) (hnm : e ∉ L) :
    L.length < eCap := by
  have h1 : (e :: L).Nodup := List.nodup_cons.mpr ⟨hnm, h.1⟩
  have h2 : (e :: L).toFinset.card = (e :: L).length := List.toFinset_card_of_nodup h1
  have h3 : (e :: L).toFinset ⊆ Finset.range eCap := fun x hx => by
    rcases List.mem_cons.mp (List.mem_toFinset.mp hx) with rfl | hxl
    · exact Finset.mem_range.mpr he
    · exact Finset.mem_range.mpr (h.2.1 x hxl)
  have h4 : (e :: L).length ≤ eCap := by
    calc (e :: L).length = (e :: L).toFinset.card := h2.symm
      _ ≤ (Finset.range eCap).card := Finset.card_le_card h3
      _ = eCap := Finset.card_range eCap
  simp only [List.length_cons] at h4; omega

lemma dedupBufAt_zero {mem : ℕ → ℕ} {flagPtr bufPtr lenAddr eCap : ℕ}
    (hfl : ∀ e < eCap, mem (flagPtr + e) = 0) (hlen : mem lenAddr = 0) :
    DedupBufAt mem flagPtr bufPtr lenAddr eCap [] :=
  ⟨List.nodup_nil, fun _ h => (by cases h), hlen, fun _ h => (by cases h),
   fun e he => by simpa using hfl e he⟩

lemma dedupBufAt_of_agree {mem₁ mem₂ : ℕ → ℕ} {flagPtr bufPtr lenAddr eCap : ℕ} {L : List ℕ}
    (h : DedupBufAt mem₁ flagPtr bufPtr lenAddr eCap L)
    (hfl : ∀ e < eCap, mem₂ (flagPtr + e) = mem₁ (flagPtr + e))
    (hbuf : ∀ i < L.length, mem₂ (bufPtr + i) = mem₁ (bufPtr + i))
    (hlen : mem₂ lenAddr = mem₁ lenAddr) :
    DedupBufAt mem₂ flagPtr bufPtr lenAddr eCap L :=
  ⟨h.1, h.2.1, hlen.trans h.2.2.1, fun i hi => (hbuf i hi).trans (h.2.2.2.1 i hi),
   fun e he => (hfl e he).trans (h.2.2.2.2 e he)⟩

@[simp] lemma mem_pushDedup_iff (L : List ℕ) (e x : ℕ) :
    x ∈ pushDedup L e ↔ x ∈ L ∨ x = e := by
  unfold pushDedup; split_ifs with h
  · constructor
    · exact Or.inl
    · rintro (hx | rfl); exact hx; exact h
  · simp

lemma appendDedup_nil (L : List ℕ) : appendDedup L [] = L := rfl
lemma appendDedup_cons (L : List ℕ) (e : ℕ) (rest : List ℕ) :
    appendDedup L (e :: rest) = appendDedup (pushDedup L e) rest := rfl
lemma appendDedup_append (L s₁ s₂ : List ℕ) :
    appendDedup L (s₁ ++ s₂) = appendDedup (appendDedup L s₁) s₂ := List.foldl_append

@[simp] lemma mem_appendDedup_iff (L src : List ℕ) (x : ℕ) :
    x ∈ appendDedup L src ↔ x ∈ L ∨ x ∈ src := by
  induction src generalizing L with
  | nil => simp [appendDedup]
  | cons a rest ih =>
    rw [appendDedup_cons, ih, mem_pushDedup_iff, List.mem_cons]
    tauto

/-! ## Verification of `asmFirstPushDedupStmt` -/

theorem asmFirstPushDedup_runs {w flagPtr bufPtr lenAddr eCap e pos : ℕ} {p : Program}
    {L : List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hD : DedupBufAt mem₀ flagPtr bufPtr lenAddr eCap L)
    (he : e < eCap)
    (hdisj_fb : flagPtr + eCap ≤ bufPtr ∨ bufPtr + eCap ≤ flagPtr)
    (hdisj_fl : lenAddr < flagPtr ∨ flagPtr + eCap ≤ lenAddr)
    (hdisj_bl : lenAddr < bufPtr ∨ bufPtr + eCap ≤ lenAddr)
    (hfl_w : flagPtr + eCap < 2 ^ w) (hbuf_w : bufPtr + eCap < 2 ^ w)
    (_hlen_w : lenAddr < 2 ^ w) :
    ∃ st' cost,
      Runs w p ω asmFirstPushDedupStmt (startState [flagPtr, bufPtr, lenAddr, e] mem₀ pos)
        (.returned 0) st' cost ∧
      DedupBufAt st'.mem flagPtr bufPtr lenAddr eCap (pushDedup L e) ∧
      (∀ a, (a < flagPtr ∨ flagPtr + eCap ≤ a) → (a < bufPtr ∨ bufPtr + eCap ≤ a) →
        a ≠ lenAddr → st'.mem a = mem₀ a) ∧
      cost ≤ 35 := by
  have h1w : 1 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  set s0 := startState [flagPtr, bufPtr, lenAddr, e] mem₀ pos
  have hfe : mem₀ (flagPtr + e) = if e ∈ L then 1 else 0 := hD.2.2.2.2 e he
  set v := if e ∈ L then 1 else 0
  set r1 := Function.update s0.regs 4 v
  have h4 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 0) (.reg 3)))) s0 .normal ⟨mem₀, r1, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]))
        (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega)) hfe, rfl, rfl, rfl⟩
  by_cases hmem : e ∈ L
  · have hv : v = 1 := by simp [v, hmem]
    have heC : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem₀, r1, pos⟩ = some 0 := by
      simp [Expr.eval, r1, hv, BinOp.eval, h0w]
    have hret : Runs w p ω (.ret (.const 0)) ⟨mem₀, r1, pos⟩ (.returned 0) ⟨mem₀, r1, pos⟩ 2 :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
    refine ⟨⟨mem₀, r1, pos⟩, 14,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, h4,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _,
          runs_cond_iff.mpr ⟨0, 1, heC, by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
          hret, rfl⟩), rfl⟩),
      by simpa [pushDedup, hmem] using hD, fun _ _ _ _ => rfl, by omega⟩
  · have hv : v = 0 := by simp [v, hmem]
    have hlt : L.length < eCap := dedupBuf_length_lt_of_not_mem hD he hmem
    have heC : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem₀, r1, pos⟩ = some 1 := by
      simp [Expr.eval, r1, hv, BinOp.eval, h0w, h1w]
    set m1 := Function.update mem₀ (flagPtr + e) 1
    set r2 := Function.update r1 5 L.length
    set m2 := Function.update m1 (bufPtr + L.length) e
    set m3 := Function.update m2 lenAddr (L.length + 1)
    have hne_fl : lenAddr ≠ flagPtr + e := by rcases hdisj_fl with h | h <;> omega
    have hne_bl : lenAddr ≠ bufPtr + L.length := by rcases hdisj_bl with h | h <;> omega
    have hne_fb : bufPtr + L.length ≠ flagPtr + e := by rcases hdisj_fb with h | h <;> omega
    have hs1 : Runs w p ω (.store (.bin .add (.reg 0) (.reg 3)) (.const 1))
        ⟨mem₀, r1, pos⟩ .normal ⟨m1, r1, pos⟩ 5 :=
      runs_store_iff.mpr ⟨flagPtr + e, 1,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, s0, startState]))
          (Expr.eval_reg_of_eq (by simp [r1, s0, startState])) (by omega),
        Expr.eval_const h1w, rfl, rfl, rfl⟩
    have hm1_len : m1 lenAddr = L.length := by
      simp only [m1, Function.update_of_ne hne_fl]; exact hD.2.2.1
    have ha5 : Runs w p ω (.assign 5 (.load (.reg 2))) ⟨m1, r1, pos⟩ .normal ⟨m1, r2, pos⟩ 3 :=
      runs_assign_iff.mpr ⟨L.length, Expr.eval_load_of_eq
        (Expr.eval_reg_of_eq (by simp [r1, s0, startState])) hm1_len, rfl, rfl, rfl⟩
    have hs2 : Runs w p ω (.store (.bin .add (.reg 1) (.reg 5)) (.reg 3))
        ⟨m1, r2, pos⟩ .normal ⟨m2, r2, pos⟩ 5 :=
      runs_store_iff.mpr ⟨bufPtr + L.length, e,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2, r1, s0, startState]))
          (Expr.eval_reg_of_eq (by simp [r2])) (by omega),
        Expr.eval_reg_of_eq (by simp [r2, r1, s0, startState]), rfl, rfl, rfl⟩
    have hs3 : Runs w p ω (.store (.reg 2) (.bin .add (.reg 5) (.const 1)))
        ⟨m2, r2, pos⟩ .normal ⟨m3, r2, pos⟩ 5 :=
      runs_store_iff.mpr ⟨lenAddr, L.length + 1,
        Expr.eval_reg_of_eq (by simp [r2, r1, s0, startState]),
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [r2])) (Expr.eval_const h1w) (by omega), rfl, rfl, rfl⟩
    have hret : Runs w p ω (.ret (.const 0)) ⟨m3, r2, pos⟩ (.returned 0) ⟨m3, r2, pos⟩ 2 :=
      runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
    refine ⟨⟨m3, r2, pos⟩, 34,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, h4,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _,
          runs_cond_iff.mpr ⟨1, 21, heC, by
            simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha5,
                runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs2, hs3, rfl⟩), rfl⟩), rfl⟩), rfl⟩,
          hret, rfl⟩), rfl⟩),
      ?_, ?_, by omega⟩
    · simp only [pushDedup, hmem, ↓reduceIte]
      refine ⟨List.nodup_append.mpr ⟨hD.1, List.nodup_singleton e, fun x hx y hy hxy =>
          hmem (by rw [← List.mem_singleton.mp hy, ← hxy]; exact hx)⟩,
        fun x hx => by
          rcases List.mem_append.mp hx with h1 | h2
          · exact hD.2.1 x h1
          · exact (List.mem_singleton.mp h2) ▸ he,
        by simp [m3],
        fun i hi => by
          simp only [List.length_append, List.length_singleton] at hi
          have hneL : bufPtr + i ≠ lenAddr := by rcases hdisj_bl with h | h <;> omega
          dsimp only [m3]; rw [Function.update_of_ne hneL]
          by_cases hil : i < L.length
          · rw [List.getElem_append_left hil]
            dsimp only [m2, m1]
            rw [Function.update_of_ne (by omega : bufPtr + i ≠ bufPtr + L.length),
              Function.update_of_ne (by rcases hdisj_fb with h | h <;> omega : bufPtr + i ≠ flagPtr + e)]
            exact hD.2.2.2.1 i hil
          · have hieq : i = L.length := by omega
            subst hieq
            rw [List.getElem_append_right (le_refl _)]
            simp [m2],
        fun e' he' => by
          have hneL : flagPtr + e' ≠ lenAddr := by rcases hdisj_fl with h | h <;> omega
          have hneB : flagPtr + e' ≠ bufPtr + L.length := by rcases hdisj_fb with h | h <;> omega
          dsimp only [m3, m2]; rw [Function.update_of_ne hneL, Function.update_of_ne hneB]
          simp only [List.mem_append, List.mem_singleton]
          by_cases hee : e' = e
          · subst hee; simp [m1]
          · simp only [m1, Function.update_of_ne (by omega : flagPtr + e' ≠ flagPtr + e), hee, or_false]
            exact hD.2.2.2.2 e' he'⟩
    · intro a h1 h2 h3
      have ha1 : a ≠ flagPtr + e := by rcases h1 with h | h <;> omega
      have ha2 : a ≠ bufPtr + L.length := by rcases h2 with h | h <;> omega
      simp [m3, m2, m1, ha1, ha2, h3]

/-! ## Verification of `asmFirstMarkSlotEdgeStmt` -/

theorem asmFirstMarkSlotEdge_runs {w gEPres hEPres inActPtr inTgtPtr eCap e pos : ℕ} {p : Program}
    {GE HE : Finset ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (he : e < eCap)
    (hGE : mem₀ (gEPres + e) = if e ∈ GE then 1 else 0)
    (hHE : mem₀ (hEPres + e) = if e ∈ HE then 1 else 0)
    (hdisj_ah : inActPtr + e ≠ hEPres + e)
    (hdisj_at : inActPtr + e ≠ inTgtPtr + e)
    (hg_w : gEPres + eCap < 2 ^ w) (hh_w : hEPres + eCap < 2 ^ w)
    (ha_w : inActPtr + eCap < 2 ^ w) (ht_w : inTgtPtr + eCap < 2 ^ w) :
    ∃ st' cost,
      Runs w p ω asmFirstMarkSlotEdgeStmt (startState [gEPres, hEPres, inActPtr, inTgtPtr, e] mem₀ pos)
        (.returned 0) st' cost ∧
      (e ∈ GE → st'.mem (inActPtr + e) = 1 ∧ st'.mem (inTgtPtr + e) = if e ∈ HE then 1 else 0) ∧
      (e ∉ GE → st'.mem = mem₀) ∧
      (∀ a, a ≠ inActPtr + e → a ≠ inTgtPtr + e → st'.mem a = mem₀ a) ∧
      cost ≤ 30 := by
  have h1w : 1 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  set s0 := startState [gEPres, hEPres, inActPtr, inTgtPtr, e] mem₀ pos
  set v := if e ∈ GE then 1 else 0
  set r1 := Function.update s0.regs 5 v
  have h5 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.reg 4)))) s0 .normal ⟨mem₀, r1, pos⟩ 5 :=
    runs_assign_iff.mpr ⟨v, Expr.eval_load_of_eq
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [s0, startState]))
        (Expr.eval_reg_of_eq (by simp [s0, startState])) (by omega)) hGE, rfl, rfl, rfl⟩
  have hret0 : ∀ m, Runs w p ω (.ret (.const 0)) ⟨m, r1, pos⟩ (.returned 0) ⟨m, r1, pos⟩ 2 := fun m =>
    runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  by_cases hmem : e ∈ GE
  · have hv : v = 1 := by simp [v, hmem]
    set m1 := Function.update mem₀ (inActPtr + e) 1
    set m2 := Function.update m1 (inTgtPtr + e) (if e ∈ HE then 1 else 0)
    have hs1 : Runs w p ω (.store (.bin .add (.reg 2) (.reg 4)) (.const 1))
        ⟨mem₀, r1, pos⟩ .normal ⟨m1, r1, pos⟩ 5 :=
      runs_store_iff.mpr ⟨inActPtr + e, 1,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, s0, startState]))
          (Expr.eval_reg_of_eq (by simp [r1, s0, startState])) (by omega),
        Expr.eval_const h1w, rfl, rfl, rfl⟩
    have hm1_h : m1 (hEPres + e) = if e ∈ HE then 1 else 0 := by
      simp only [m1, Function.update_of_ne hdisj_ah.symm]; exact hHE
    have hs2 : Runs w p ω (.store (.bin .add (.reg 3) (.reg 4)) (.load (.bin .add (.reg 1) (.reg 4))))
        ⟨m1, r1, pos⟩ .normal ⟨m2, r1, pos⟩ 8 :=
      runs_store_iff.mpr ⟨inTgtPtr + e, if e ∈ HE then 1 else 0,
        Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, s0, startState]))
          (Expr.eval_reg_of_eq (by simp [r1, s0, startState])) (by omega),
        Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by simp [r1, s0, startState]))
          (Expr.eval_reg_of_eq (by simp [r1, s0, startState])) (by omega)) hm1_h, rfl, rfl, rfl⟩
    refine ⟨⟨m2, r1, pos⟩, 25,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, h5,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _,
          runs_cond_iff.mpr ⟨1, 14, Expr.eval_reg_of_eq (by simp [r1, hv]), by
            simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, hs1, hs2, rfl⟩), rfl⟩,
          hret0 m2, rfl⟩), rfl⟩),
      fun _ => ⟨by dsimp only [m2]; rw [Function.update_of_ne hdisj_at]; simp [m1], by simp [m2]⟩,
      fun h => absurd hmem h,
      fun a h1 h2 => by simp [m2, m1, h1, h2],
      by omega⟩
  · have hv : v = 0 := by simp [v, hmem]
    refine ⟨⟨mem₀, r1, pos⟩, 12,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, h5,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _,
          runs_cond_iff.mpr ⟨0, 1, Expr.eval_reg_of_eq (by simp [r1, hv]),
            by simpa using runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩, rfl⟩,
          hret0 mem₀, rfl⟩), rfl⟩),
      fun h => absurd h hmem, fun _ => rfl, fun _ _ _ => rfl, by omega⟩

/-! ## Verification of `asmFirstAppendListStmt` -/

theorem asmFirstAppendList_runs {w fPush flagPtr bufPtr lenAddr srcPtr eCap pos : ℕ} {p : Program}
    (hfPush : p.procs[fPush]? = some asmFirstPushDedupStmt)
    {L src : List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hD : DedupBufAt mem₀ flagPtr bufPtr lenAddr eCap L)
    (hSrc : ListAt mem₀ srcPtr src)
    (hSrc_cap : ∀ e ∈ src, e < eCap)
    (hdisj_fb : flagPtr + eCap ≤ bufPtr ∨ bufPtr + eCap ≤ flagPtr)
    (hdisj_fl : lenAddr < flagPtr ∨ flagPtr + eCap ≤ lenAddr)
    (hdisj_bl : lenAddr < bufPtr ∨ bufPtr + eCap ≤ lenAddr)
    (hdisj_sf : srcPtr + src.length ≤ flagPtr ∨ flagPtr + eCap ≤ srcPtr)
    (hdisj_sb : srcPtr + src.length ≤ bufPtr ∨ bufPtr + eCap ≤ srcPtr)
    (hdisj_sl : lenAddr < srcPtr ∨ srcPtr + src.length ≤ lenAddr)
    (hfl_w : flagPtr + eCap < 2 ^ w) (hbuf_w : bufPtr + eCap < 2 ^ w)
    (hlen_w : lenAddr < 2 ^ w) (hsrc_w : srcPtr + src.length < 2 ^ w) :
    ∃ st' cost,
      Runs w p ω (asmFirstAppendListStmt fPush)
        (startState [flagPtr, bufPtr, lenAddr, srcPtr, src.length] mem₀ pos) (.returned 0) st' cost ∧
      DedupBufAt st'.mem flagPtr bufPtr lenAddr eCap (appendDedup L src) ∧
      (∀ a, (a < flagPtr ∨ flagPtr + eCap ≤ a) → (a < bufPtr ∨ bufPtr + eCap ≤ a) →
        a ≠ lenAddr → st'.mem a = mem₀ a) ∧
      cost ≤ 60 * src.length + 20 := by
  have h1w : 1 < 2 ^ w := by omega
  have h0w : 0 < 2 ^ w := by omega
  let inv : ℕ → State → Prop := fun i st =>
    st.regs 0 = flagPtr ∧ st.regs 1 = bufPtr ∧ st.regs 2 = lenAddr ∧
    st.regs 3 = srcPtr ∧ st.regs 4 = src.length ∧ st.regs 5 = i ∧
    DedupBufAt st.mem flagPtr bufPtr lenAddr eCap (appendDedup L (src.take i)) ∧
    (∀ a, (a < flagPtr ∨ flagPtr + eCap ≤ a) → (a < bufPtr ∨ bufPtr + eCap ≤ a) →
      a ≠ lenAddr → st.mem a = mem₀ a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 5) (lo := .const 0) (hi := .reg 4)
    (body := .assign 6 (.load (.bin .add (.reg 3) (.reg 5))) ;;
      .call 7 fPush [.reg 0, .reg 1, .reg 2, .reg 6])
    (P := fun st => inv 0 { st with regs := Function.update st.regs 5 0 })
    (Inv := inv) (fun _ => 48) 0 src.length (Nat.zero_le _) h1w (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const h0w, hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.2.2.2.1)
    (fun i _ hi st ω' ⟨r0, r1, r2, r3, r4, r5, hDi, hfri⟩ => by
      set e := src[i]'hi
      have heCap : e < eCap := hSrc_cap e (List.getElem_mem hi)
      have hme : st.mem (srcPtr + i) = e := by
        rw [hfri (srcPtr + i) (by rcases hdisj_sf with h | h <;> omega)
          (by rcases hdisj_sb with h | h <;> omega) (by rcases hdisj_sl with h | h <;> omega)]
        exact hSrc i hi
      set rA := Function.update st.regs 6 e
      have h6 : Runs w p ω' (.assign 6 (.load (.bin .add (.reg 3) (.reg 5)))) st .normal ⟨st.mem, rA, st.pos⟩ 5 :=
        runs_assign_iff.mpr ⟨e, Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq r3) (Expr.eval_reg_of_eq r5) (by omega)) hme, rfl, rfl, rfl⟩
      obtain ⟨st1, c1, hr1, hD1, hfr1, hc1⟩ := asmFirstPushDedup_runs (p := p) (ω := ω') (pos := st.pos)
        hw16 hDi heCap hdisj_fb hdisj_fl hdisj_bl hfl_w hbuf_w hlen_w
      have hLlen : (appendDedup L (src.take i)).length ≤ eCap := dedupBuf_length_le hDi
      have heArgs : evalArgs w ⟨st.mem, rA, st.pos⟩ [.reg 0, .reg 1, .reg 2, .reg 6] =
          some [flagPtr, bufPtr, lenAddr, e] :=
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, r0])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, r1])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA, r2])) <|
        evalArgs_cons (Expr.eval_reg_of_eq (by simp [rA])) <| evalArgs_nil _ _
      have hcall : Runs w p ω' (.call 7 fPush [.reg 0, .reg 1, .reg 2, .reg 6])
          ⟨st.mem, rA, st.pos⟩ .normal ⟨st1.mem, Function.update rA 7 0, st1.pos⟩
          (argsSize [.reg 0, .reg 1, .reg 2, .reg 6] + c1 + 1) :=
        runs_call_iff.mpr ⟨_, asmFirstPushDedupStmt, .returned 0, st1, c1, heArgs, hfPush, hr1, rfl, rfl, rfl⟩
      have htk : appendDedup L (src.take (i + 1)) = pushDedup (appendDedup L (src.take i)) e := by
        rw [List.take_succ_eq_append_getElem hi, appendDedup_append]; rfl
      refine ⟨.normal, ⟨st1.mem, Function.update rA 7 0, st1.pos⟩,
        5 + (argsSize [.reg 0, .reg 1, .reg 2, .reg 6] + c1 + 1) + 1,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, h6, hcall, rfl⟩),
        ⟨⟨by simp [rA, r0], by simp [rA, r1], by simp [rA, r2], by simp [rA, r3], by simp [rA, r4],
          by simp, htk ▸ hD1, fun a haf hab hal => ?_⟩, by simp [rA, r5]⟩,
        by show 5 + (argsSize [.reg 0, .reg 1, .reg 2, .reg 6] + c1 + 1) + 1 ≤ 48
           simp only [argsSize, Expr.size]; omega⟩
      rw [hfr1 a haf hab hal]
      exact hfri a haf hab hal)
  set s0 := startState [flagPtr, bufPtr, lenAddr, srcPtr, src.length] mem₀ pos
  obtain ⟨o, st1, c1, hr1, hpost1, hc1⟩ := hloop s0 ω
    ⟨by simp [s0, startState], by simp [s0, startState], by simp [s0, startState],
     by simp [s0, startState], by simp [s0, startState], by simp,
     by simpa [s0, startState, appendDedup] using hD, fun _ _ _ _ => rfl⟩
  cases o with
  | returned _ => cases hpost1
  | normal =>
  obtain ⟨-, -, -, -, -, -, hDf, hfrf⟩ := hpost1
  rw [List.take_length] at hDf
  have hret : Runs w p ω (.ret (.const 0)) st1 (.returned 0) st1 2 :=
    runs_ret_iff.mpr ⟨0, Expr.eval_const h0w, rfl, rfl, rfl⟩
  have hrc : rangeCost (fun _ => 48) 0 src.length = 48 * src.length := by
    simp [rangeCost, Nat.mul_comm]
  dsimp only at hc1; simp only [hrc, Nat.sub_zero, Expr.size] at hc1
  exact ⟨st1, c1 + 2 + 1, runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr1, hret, rfl⟩), hDf, hfrf, by omega⟩

end

end MinCostFlow.SparseCore.Program
