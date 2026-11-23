module

public import MinCostFlow.MinRatio.TreeEditLayout
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
import WordRAM.Tactic
import WordRAM.Memory

/-!
# Packing a rebuilt forest difference

Lemma 5.11 (page 20) reports deleted and inserted edge names. When
rebuilding a forest, scan its live names and test each one in the
opposite graph's presence table. The following kernel appends the
two-word record for a name absent from that table.
-/

public section
namespace MinCostFlow.MinRatio

open WordRAM

/-- The output cursor is register 6, the tag is register 7, the edge
name is register 8, and register 18 counts records written so far. -/
@[expose] def treeEditPackAppend : Stmt :=
  .store (.reg 6) (.reg 7) ;;
  .store (.bin .add (.reg 6) (.const 1)) (.reg 8) ;;
  .assign 6 (.bin .add (.reg 6) (.const 2)) ;;
  .assign 18 (.bin .add (.reg 18) (.const 1))

/-- Test the current name in the opposite presence table at base
register 9. A zero cell means that this name belongs in the difference. -/
@[expose] def treeEditPackName : Stmt :=
  .cond (.load (.bin .add (.reg 9) (.reg 8))) .nop treeEditPackAppend

/-- One presence test costs at most 25 steps, including a possible
append. The append changes precisely two memory cells and increments
the cursor and count. -/
theorem treeEditPackName_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hlookup : st.regs 9 + st.regs 8 < 2 ^ w)
    (hcursor : st.regs 6 + 2 < 2 ^ w) (hcount : st.regs 18 + 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω treeEditPackName st .normal out cost ∧ cost ≤ 25 ∧
      out = if st.mem (st.regs 9 + st.regs 8) = 0 then
        { st with
          mem := Function.update (Function.update st.mem (st.regs 6) (st.regs 7))
            (st.regs 6 + 1) (st.regs 8)
          regs := Function.update (Function.update st.regs 6 (st.regs 6 + 2))
            18 (st.regs 18 + 1) }
        else st := by
  have h1 : 1 < 2 ^ w := by omega
  have h2 : 2 < 2 ^ w := by omega
  have ha : st.regs 6 + 1 < 2 ^ w := by omega
  suffices hh : ∃ o out cost, Runs w p ω treeEditPackName st o out cost ∧
      (o = .normal ∧ out = if st.mem (st.regs 9 + st.regs 8) = 0 then
        { st with
          mem := Function.update (Function.update st.mem (st.regs 6) (st.regs 7))
            (st.regs 6 + 1) (st.regs 8)
          regs := Function.update (Function.update st.regs 6 (st.regs 6 + 2))
            18 (st.regs 18 + 1) }
        else st) ∧ 0 + cost ≤ 25 by
    obtain ⟨_, out, c, hr, ⟨rfl, he⟩, hc⟩ := hh
    exact ⟨out, c, hr, by simpa using hc, he⟩
  unfold treeEditPackName
  refine runs_cond_le (v := st.mem (st.regs 9 + st.regs 8))
    (by simp [Expr.eval, BinOp.eval, hlookup]) ?_ ?_
  · intro hn
    exact runs_nop_le (by simp [hn]) (by decide)
  · intro hz
    unfold treeEditPackAppend
    refine runs_seq_store_le (x := st.regs 6) (v := st.regs 7) (by rfl) (by rfl) ?_
    refine runs_seq_store_le (x := st.regs 6 + 1) (v := st.regs 8)
      (by simp [Expr.eval, BinOp.eval, h1, ha]) (by rfl) ?_
    refine runs_seq_assign_le (v := st.regs 6 + 2)
      (by simp [Expr.eval, BinOp.eval, h2, hcursor]) ?_
    refine runs_assign_le (v := st.regs 18 + 1)
      (by simp [Expr.eval, BinOp.eval, h1, hcount, Function.update_of_ne]) ?_ (by decide)
    simp [hz]

/-- Registers 10 and 11 are the source cursor and remaining count.
The presence test handles the loaded name before advancing the source. -/
@[expose] def treeEditPackStep : Stmt :=
  .assign 8 (.load (.reg 10)) ;;
  treeEditPackName ;;
  .assign 10 (.bin .add (.reg 10) (.const 1)) ;;
  .assign 11 (.bin .sub (.reg 11) (.const 1))

/-- The scan consumes one input word and either leaves the output
unchanged or appends its tag and name. -/
theorem treeEditPackStep_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hSrc : st.regs 10 + 1 < 2 ^ w) (hRemaining : st.regs 11 < 2 ^ w)
    (hlookup : st.regs 9 + st.mem (st.regs 10) < 2 ^ w)
    (hcursor : st.regs 6 + 2 < 2 ^ w) (hcount : st.regs 18 + 1 < 2 ^ w) :
    let e := st.mem (st.regs 10)
    let fresh := st.mem (st.regs 9 + e) = 0
    ∃ out cost, Runs w p ω treeEditPackStep st .normal out cost ∧ cost ≤ 39 ∧
      out.regs 10 = st.regs 10 + 1 ∧ out.regs 11 = st.regs 11 - 1 ∧
      out.regs 6 = st.regs 6 + (if fresh then 2 else 0) ∧
      out.regs 18 = st.regs 18 + (if fresh then 1 else 0) ∧
      (∀ r, r ≠ 6 → r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ 18 → out.regs r = st.regs r) ∧
      out.mem = if fresh then
        Function.update (Function.update st.mem (st.regs 6) (st.regs 7)) (st.regs 6 + 1) e
        else st.mem := by
  dsimp only
  let e := st.mem (st.regs 10)
  let loaded := { st with regs := Function.update st.regs 8 e }
  have hload : Runs w p ω (.assign 8 (.load (.reg 10))) st .normal loaded 3 :=
    runs_assign_iff.mpr ⟨e, rfl, rfl, rfl, rfl⟩
  obtain ⟨mid, c, hp, hc, hmid⟩ :=
    treeEditPackName_runs (st := loaded) (p := p) (ω := ω)
      (by simpa [loaded, e, Function.update_of_ne] using hlookup)
      (by simpa [loaded, Function.update_of_ne] using hcursor)
      (by simpa [loaded, Function.update_of_ne] using hcount)
  simp only [loaded, Function.update_self, Function.update_of_ne (show 9 ≠ 8 by decide),
    Function.update_of_ne (show 6 ≠ 8 by decide), Function.update_of_ne (show 7 ≠ 8 by decide),
    Function.update_of_ne (show 18 ≠ 8 by decide)] at hmid
  let step := { mid with regs := Function.update mid.regs 10 (st.regs 10 + 1) }
  let out := { step with regs := Function.update step.regs 11 (st.regs 11 - 1) }
  have h10 : mid.regs 10 = st.regs 10 := by split at hmid <;> simp [hmid, Function.update_of_ne]
  have h11 : step.regs 11 = st.regs 11 := by
    split at hmid <;> simp [step, hmid, Function.update_of_ne]
  have hone : 1 < 2 ^ w := by omega
  have hsub : st.regs 11 - 1 < 2 ^ w := by omega
  have ha : Runs w p ω (.assign 10 (.bin .add (.reg 10) (.const 1))) mid .normal step 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h10, hone, hSrc], rfl, rfl, rfl⟩
  have hb : Runs w p ω (.assign 11 (.bin .sub (.reg 11) (.const 1))) step .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, h11, hone, hsub], rfl, rfl, rfl⟩
  refine ⟨out, c + 14, runs_seq_iff.mpr (Or.inr ⟨loaded, 3, c + 10, hload,
    runs_seq_iff.mpr (Or.inr ⟨mid, c, 9, hp,
      runs_seq_iff.mpr (Or.inr ⟨step, 4, 4, ha, hb, rfl⟩), rfl⟩), by omega⟩),
    by omega, by simp [out, step, Function.update_of_ne], by simp [out], ?_, ?_, ?_, ?_⟩
  · split at hmid <;> simp_all [out, step, loaded, e, Function.update_of_ne]
  · split at hmid <;> simp_all [out, step, loaded, e, Function.update_of_ne]
  · intro r h6 h8 h10 h11 h18
    split at hmid <;> simp [out, step, hmid, Function.update_of_ne, h6, h8, h10, h11, h18]
  · split at hmid <;> simp_all [out, step, loaded, e, Function.update_of_ne]

/-- Scan the remaining source names and append their packed edits. -/
@[expose] def treeEditPackScan : Stmt :=
  .loop (.reg 11) treeEditPackStep

/-- The words appended by a scan in its stored order. -/
@[expose] def treeEditPackWords (tag : ℕ) (absent : ℕ → Bool) (edges : List ℕ) : List ℕ :=
  (edges.filter absent).flatMap fun e => [tag, e]

/-- Each scanned name contributes at most two output words. -/
theorem treeEditPackWords_length_le (tag : ℕ) (absent : ℕ → Bool) (edges : List ℕ) :
    (treeEditPackWords tag absent edges).length ≤ 2 * edges.length := by
  induction edges with
  | nil => simp [treeEditPackWords]
  | cons e edges ih =>
    cases h : absent e <;> simp [treeEditPackWords, h] at * <;> omega

/-- A scan writes just the packed difference records. Its source
and lookups are outside the reserved output interval. -/
theorem treeEditPackScan_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (edges : List ℕ) (absent : ℕ → Bool)
    (hSource : ListAt st.mem (st.regs 10) edges)
    (hLen : st.regs 11 = edges.length)
    (hSrcRoom : st.regs 10 + edges.length < 2 ^ w)
    (hOutRoom : st.regs 6 + 2 * edges.length < 2 ^ w)
    (hCountRoom : st.regs 18 + edges.length < 2 ^ w)
    (hSep : ∀ a, st.regs 10 ≤ a → a < st.regs 10 + edges.length →
      a < st.regs 6 ∨ st.regs 6 + 2 * edges.length ≤ a)
    (hLookup : ∀ e ∈ edges,
      st.regs 9 + e < 2 ^ w ∧
      (st.mem (st.regs 9 + e) = 0 ↔ absent e = true) ∧
      (st.regs 9 + e < st.regs 6 ∨ st.regs 6 + 2 * edges.length ≤ st.regs 9 + e)) :
    let words := treeEditPackWords (st.regs 7) absent edges
    ∃ out cost, Runs w p ω treeEditPackScan st .normal out cost ∧ cost ≤ 41 * edges.length + 2 ∧
      out.regs 10 = st.regs 10 + edges.length ∧ out.regs 11 = 0 ∧
      out.regs 6 = st.regs 6 + words.length ∧ out.regs 18 = st.regs 18 + (edges.filter absent).length ∧
      (∀ r, r ≠ 6 → r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ 18 → out.regs r = st.regs r) ∧
      ListAt out.mem (st.regs 6) words ∧
      (∀ a, a < st.regs 6 ∨ st.regs 6 + words.length ≤ a → out.mem a = st.mem a) := by
  dsimp only
  induction edges generalizing st with
  | nil =>
    have hz : (Expr.reg 11).eval w st = some 0 := by simp [Expr.eval, hLen]
    exact ⟨st, 2, runs_loop_iff.mpr (Or.inl ⟨hz, rfl, rfl, rfl⟩),
      by simp, by simp, hLen, by simp [treeEditPackWords], by simp,
      fun _ _ _ _ _ _ => rfl, listAt_nil _ _, fun _ _ => rfl⟩
  | cons e rest ih =>
    obtain ⟨he, ht⟩ := listAt_cons.mp hSource
    obtain ⟨hl, hm, hLookupSep⟩ := hLookup e List.mem_cons_self
    obtain ⟨mid, c, hr, hc, hs, hc', ho, hn, hregs, hmem⟩ :=
      treeEditPackStep_runs (w := w) (p := p) (ω := ω) (st := st)
        (by simp only [List.length_cons] at hSrcRoom; omega)
        (by rw [hLen]; omega) (by rwa [he])
        (by simp only [List.length_cons] at hOutRoom; omega)
        (by simp only [List.length_cons] at hCountRoom; omega)
    rw [he] at ho hn hmem
    let k := if absent e then 2 else 0
    let added := if absent e then 1 else 0
    have hout : mid.regs 6 = st.regs 6 + k := by simpa only [hm, Bool.coe_iff_coe] using ho
    have hnum : mid.regs 18 = st.regs 18 + added := by simpa only [hm, Bool.coe_iff_coe] using hn
    have hk : k ≤ 2 := by cases h : absent e <;> simp [k, h]
    have hadd : added ≤ 1 := by cases h : absent e <;> simp [added, h]
    have h9 := hregs 9 (by decide) (by decide) (by decide) (by decide) (by decide)
    have h7 := hregs 7 (by decide) (by decide) (by decide) (by decide) (by decide)
    have hframe a (ha : a < st.regs 6 ∨ st.regs 6 + k ≤ a) : mid.mem a = st.mem a := by
      rw [hmem]
      by_cases hzero : st.mem (st.regs 9 + e) = 0
      · have htrue := hm.mp hzero
        simp [k, htrue] at ha
        rw [ite_eq_left hzero, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
      · rw [ite_eq_right hzero]
    have hsepAux a (ha : a < st.regs 6 ∨ st.regs 6 + 2 * (e :: rest).length ≤ a) :
        a < st.regs 6 ∨ st.regs 6 + k ≤ a := by
      simp only [List.length_cons] at ha
      omega
    have ht' : ListAt mid.mem (mid.regs 10) rest := by
      rw [hs]
      intro i hi
      rw [hframe _ (hsepAux _ (hSep _ (by omega) (by simp only [List.length_cons]; omega)))]
      exact ht i hi
    have hlook' : ∀ f ∈ rest,
        mid.regs 9 + f < 2 ^ w ∧
        (mid.mem (mid.regs 9 + f) = 0 ↔ absent f = true) ∧
        (mid.regs 9 + f < mid.regs 6 ∨ mid.regs 6 + 2 * rest.length ≤ mid.regs 9 + f) := by
      intro f hf
      obtain ⟨ha, hb, hh⟩ := hLookup f (List.mem_cons_of_mem _ hf)
      rw [h9, hout, hframe _ (hsepAux _ hh)]
      simp only [List.length_cons] at hh
      exact ⟨ha, hb, by omega⟩
    obtain ⟨out, d, hrun, hd, houtSrc, houtLen, houtBase, houtNum, houtReg, hwords, houtMem⟩ :=
      ih ht' (by rw [hc', hLen, List.length_cons]; omega)
        (by rw [hs]; simp only [List.length_cons] at hSrcRoom; omega)
        (by rw [hout]; simp only [List.length_cons] at hOutRoom; omega)
        (by rw [hnum]; simp only [List.length_cons] at hCountRoom; omega)
        (by intro a ha hb; rw [hs] at ha hb; rw [hout]
            have h := hSep a (by omega) (by simp only [List.length_cons]; omega)
            simp only [List.length_cons] at h
            omega) hlook'
    have htest : (Expr.reg 11).eval w st = some (rest.length + 1) := by simp [Expr.eval, hLen]
    rw [h7] at houtBase hwords houtMem
    have hwordsLen : (treeEditPackWords (st.regs 7) absent (e :: rest)).length =
        k + (treeEditPackWords (st.regs 7) absent rest).length := by
      cases h : absent e <;> simp [treeEditPackWords, k, h] ; omega
    have hfilterLen : ((e :: rest).filter absent).length = added + (rest.filter absent).length := by
      cases h : absent e <;> simp [added, h] ; omega
    refine ⟨out, c + 2 + d, runs_loop_iff.mpr (Or.inr (Or.inr ⟨rest.length + 1, mid, c, d,
      htest, Nat.succ_ne_zero _, hr, hrun, by simp [Expr.size]; omega⟩)), ?_, ?_, houtLen, ?_, ?_,
      fun r h6 h8 h10 h11 h18 => (houtReg r h6 h8 h10 h11 h18).trans (hregs r h6 h8 h10 h11 h18),
      ?_, ?_⟩
    · simp only [List.length_cons, Nat.mul_add, Nat.mul_one]
      omega
    · rw [houtSrc, hs, List.length_cons]
      omega
    · rw [houtBase, hout, hwordsLen, Nat.add_assoc]
    · rw [houtNum, hnum, hfilterLen, Nat.add_assoc]
    · cases hf : absent e
      · simpa [treeEditPackWords, hf, hout, k] using hwords
      · have hz := hm.mpr hf
        have hmid1 : mid.mem (st.regs 6) = st.regs 7 := by simp [hmem, hz, Function.update_of_ne]
        have hmid2 : mid.mem (st.regs 6 + 1) = e := by simp [hmem, hz]
        have hb : mid.regs 6 = st.regs 6 + 2 := by simpa [k, hf] using hout
        rw [hb] at hwords
        have hb1 := houtMem (st.regs 6) (Or.inl (by omega))
        have hb2 := houtMem (st.regs 6 + 1) (Or.inl (by omega))
        simp only [treeEditPackWords, List.filter_cons, hf, ite_true, List.flatMap_cons]
        exact listAt_append.mpr ⟨listAt_cons.mpr ⟨hb1.trans hmid1,
          listAt_singleton.mpr (hb2.trans hmid2)⟩, hwords⟩
    · intro a ha
      rw [hwordsLen] at ha
      have hA : a < mid.regs 6 ∨ mid.regs 6 + (treeEditPackWords (st.regs 7) absent rest).length ≤ a := by
        rw [hout]
        omega
      exact (houtMem a hA).trans (hframe a (by omega))

/-- Use the new forest's source cursor and count and the old
forest's presence base for the insertion pass. -/
@[expose] def treeEditPackSwitch : Stmt :=
  .assign 10 (.reg 12) ;;
  .assign 11 (.reg 13) ;;
  .assign 9 (.reg 14) ;;
  .assign 7 (.const 1)

/-- The second pass changes just four argument registers. -/
theorem treeEditPackSwitch_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} (st : State)
    (hone : 1 < 2 ^ w) :
    ∃ out, Runs w p ω treeEditPackSwitch st .normal out 11 ∧
      out.mem = st.mem ∧ out.regs 10 = st.regs 12 ∧ out.regs 11 = st.regs 13 ∧
      out.regs 9 = st.regs 14 ∧ out.regs 7 = 1 ∧
      (∀ r, r ≠ 7 → r ≠ 9 → r ≠ 10 → r ≠ 11 → out.regs r = st.regs r) := by
  let a := { st with regs := Function.update st.regs 10 (st.regs 12) }
  let b := { a with regs := Function.update a.regs 11 (st.regs 13) }
  let c := { b with regs := Function.update b.regs 9 (st.regs 14) }
  let out := { c with regs := Function.update c.regs 7 1 }
  have ha : Runs w p ω (.assign 10 (.reg 12)) st .normal a 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hb : Runs w p ω (.assign 11 (.reg 13)) a .normal b 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a, Function.update_of_ne], rfl, rfl, rfl⟩
  have hc : Runs w p ω (.assign 9 (.reg 14)) b .normal c 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a, b, Function.update_of_ne], rfl, rfl, rfl⟩
  have hd : Runs w p ω (.assign 7 (.const 1)) c .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hone], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨a, 2, 8, ha,
    runs_seq_iff.mpr (Or.inr ⟨b, 2, 5, hb,
      runs_seq_iff.mpr (Or.inr ⟨c, 2, 2, hc, hd, rfl⟩), rfl⟩), rfl⟩), rfl,
    by simp [out, c, b, a, Function.update_of_ne], by simp [out, c, b, Function.update_of_ne],
    by simp [out, c, Function.update_of_ne], by simp [out], ?_⟩
  intro r h7 h9 h10 h11
  simp [out, c, b, a, Function.update_of_ne, h7, h9, h10, h11]

/-- Pack deletions first and insertions second in the same buffer. -/
@[expose] def treeEditPackBoth : Stmt :=
  treeEditPackScan ;; treeEditPackSwitch ;; treeEditPackScan

/-- One source list and its opposite membership table, protected from
writes to the output interval. -/
structure TreeEditPackSource (w : ℕ) (mem : ℕ → ℕ) (source lookup lo hi : ℕ)
    (edges : List ℕ) (absent : ℕ → Bool) : Prop where
  words : ListAt mem source edges
  room : source + edges.length < 2 ^ w
  sourceOutside : ∀ a, source ≤ a → a < source + edges.length → a < lo ∨ hi ≤ a
  lookups : ∀ e ∈ edges, lookup + e < 2 ^ w ∧
    (mem (lookup + e) = 0 ↔ absent e = true) ∧ (lookup + e < lo ∨ hi ≤ lookup + e)

/-- Readiness of the second pass survives the writes of the first pass. -/
theorem TreeEditPackSource.congr {w : ℕ} {mem mem' : ℕ → ℕ} {source lookup lo hi : ℕ}
    {edges : List ℕ} {absent : ℕ → Bool}
    (h : TreeEditPackSource w mem source lookup lo hi edges absent)
    (hf : ∀ a, a < lo ∨ hi ≤ a → mem' a = mem a) :
    TreeEditPackSource w mem' source lookup lo hi edges absent := by
  refine ⟨h.words.congr (fun a hlo hhi => hf a (h.sourceOutside a hlo hhi)), h.room,
    h.sourceOutside, ?_⟩
  intro e he
  obtain ⟨hroom, hm, hsep⟩ := h.lookups e he
  exact ⟨hroom, by rw [hf _ hsep]; exact hm, hsep⟩

/-- A scan may consume part of a common output allocation. -/
theorem TreeEditPackSource.scan {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State} {lo hi : ℕ}
    {edges : List ℕ} {absent : ℕ → Bool}
    (h : TreeEditPackSource w st.mem (st.regs 10) (st.regs 9) lo hi edges absent)
    (hlen : st.regs 11 = edges.length)
    (hlo : lo ≤ st.regs 6) (hhi : st.regs 6 + 2 * edges.length ≤ hi) (hw : hi < 2 ^ w)
    (hc : st.regs 18 + edges.length < 2 ^ w) :
    let words := treeEditPackWords (st.regs 7) absent edges
    ∃ out cost, Runs w p ω treeEditPackScan st .normal out cost ∧ cost ≤ 41 * edges.length + 2 ∧
      out.regs 6 = st.regs 6 + words.length ∧ out.regs 18 = st.regs 18 + (edges.filter absent).length ∧
      (∀ r, r ≠ 6 → r ≠ 8 → r ≠ 10 → r ≠ 11 → r ≠ 18 → out.regs r = st.regs r) ∧
      ListAt out.mem (st.regs 6) words ∧
      (∀ a, a < st.regs 6 ∨ st.regs 6 + words.length ≤ a → out.mem a = st.mem a) := by
  obtain ⟨out, c, hr, hcost, _, _, h6, h18, hregs, hwords, hf⟩ :=
    treeEditPackScan_runs (p := p) (ω := ω) edges absent h.words hlen h.room (hhi.trans_lt hw) hc
      (fun a ha hb => (h.sourceOutside a ha hb).imp (·.trans_le hlo) (hhi.trans ·))
      (fun e he => let ⟨hw, hm, hs⟩ := h.lookups e he
        ⟨hw, hm, hs.imp (·.trans_le hlo) (hhi.trans ·)⟩)
  exact ⟨out, c, hr, hcost, h6, h18, hregs, hwords, hf⟩

/-- The two rebuild scans append the exact deletion and insertion
blocks and preserve all memory outside their combined output. -/
theorem treeEditPackBoth_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (oldNames newNames : List ℕ) (deleted inserted : ℕ → Bool)
    (hOld : TreeEditPackSource w st.mem (st.regs 10) (st.regs 9) (st.regs 6)
      (st.regs 6 + 2 * (oldNames.length + newNames.length)) oldNames deleted)
    (hNew : TreeEditPackSource w st.mem (st.regs 12) (st.regs 14) (st.regs 6)
      (st.regs 6 + 2 * (oldNames.length + newNames.length)) newNames inserted)
    (h10 : st.regs 11 = oldNames.length) (h13 : st.regs 13 = newNames.length)
    (hTag : st.regs 7 = 0) (hw : 1 < 2 ^ w)
    (hRoom : st.regs 6 + 2 * (oldNames.length + newNames.length) < 2 ^ w)
    (hCount : st.regs 18 + oldNames.length + newNames.length < 2 ^ w) :
    let words := treeEditPackWords 0 deleted oldNames ++ treeEditPackWords 1 inserted newNames
    ∃ out cost, Runs w p ω treeEditPackBoth st .normal out cost ∧
      cost ≤ 41 * (oldNames.length + newNames.length) + 17 ∧
      out.regs 6 = st.regs 6 + words.length ∧
      out.regs 18 = st.regs 18 + (oldNames.filter deleted).length + (newNames.filter inserted).length ∧
      ListAt out.mem (st.regs 6) words ∧
      (∀ r, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 18 →
        out.regs r = st.regs r) ∧
      ∀ a, a < st.regs 6 ∨ st.regs 6 + words.length ≤ a → out.mem a = st.mem a := by
  dsimp only
  obtain ⟨mid, c, hc, hcost, h6, h18, hregs, hOldAt, hframe⟩ :=
    hOld.scan (p := p) (ω := ω) h10 le_rfl (by omega) hRoom (by omega)
  rw [hTag] at h6 hOldAt hframe
  have hl := treeEditPackWords_length_le 0 deleted oldNames
  obtain ⟨ready, hs, hmem, hs10, hs11, hs9, hs7, hsRegs⟩ :=
    treeEditPackSwitch_runs (p := p) (ω := ω) mid hw
  have hr6 := (hsRegs 6 (by decide) (by decide) (by decide) (by decide)).trans h6
  have hr18 := (hsRegs 18 (by decide) (by decide) (by decide) (by decide)).trans h18
  have hNewReady : TreeEditPackSource w ready.mem (ready.regs 10) (ready.regs 9) (st.regs 6)
      (st.regs 6 + 2 * (oldNames.length + newNames.length)) newNames inserted := by
    rw [hs10, hs9, hregs 12 (by decide) (by decide) (by decide) (by decide) (by decide),
      hregs 14 (by decide) (by decide) (by decide) (by decide) (by decide), hmem]
    exact hNew.congr (fun a ha => hframe a (by omega))
  have hlen := hs11.trans ((hregs 13 (by decide) (by decide) (by decide) (by decide) (by decide)).trans h13)
  have hnd := List.length_filter_le deleted oldNames
  obtain ⟨out, d, hd, hdCost, hd6, hd18, hdRegs, hNewAt, hframe'⟩ :=
    hNewReady.scan (p := p) (ω := ω) hlen (by omega) (by omega) hRoom (by omega)
  rw [hs7, hr6] at hd6 hNewAt hframe'
  have hkeep : ListAt out.mem (st.regs 6) (treeEditPackWords 0 deleted oldNames) := by
    apply hOldAt.congr
    intro a _ hhi
    exact (hframe' a (Or.inl hhi)).trans (congrFun hmem a)
  refine ⟨out, c + (11 + d + 1) + 1,
    runs_seq_iff.mpr (Or.inr ⟨mid, c, _, hc,
      runs_seq_iff.mpr (Or.inr ⟨ready, 11, d, hs, hd, rfl⟩), rfl⟩),
    ?_, ?_, ?_, listAt_append.mpr ⟨hkeep, hNewAt⟩, ?_, ?_⟩
  · rw [Nat.mul_add]
    omega
  · rw [hd6, List.length_append, Nat.add_assoc]
  · rw [hd18, hr18]
  · intro r h6 h7 h8 h9 h10 h11 h18
    exact (hdRegs r h6 h8 h10 h11 h18).trans
      ((hsRegs r h7 h9 h10 h11).trans (hregs r h6 h8 h10 h11 h18))
  · intro a ha
    rw [List.length_append] at ha
    exact (hframe' a (by omega)).trans ((congrFun hmem a).trans (hframe a (by omega)))

/-- With the presence tests for the two edge sets, the scan's
output is an input to the ordered Cut and Link fold. -/
theorem treeEditPackBoth_difference {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {oldE newE : Finset ℕ} {oldNames newNames : List ℕ}
    (ho : oldNames.Perm oldE.toList) (hn : newNames.Perm newE.toList)
    (hOld : TreeEditPackSource w st.mem (st.regs 10) (st.regs 9) (st.regs 6)
      (st.regs 6 + 2 * (oldNames.length + newNames.length)) oldNames (fun e => decide (e ∉ newE)))
    (hNew : TreeEditPackSource w st.mem (st.regs 12) (st.regs 14) (st.regs 6)
      (st.regs 6 + 2 * (oldNames.length + newNames.length)) newNames (fun e => decide (e ∉ oldE)))
    (h10 : st.regs 11 = oldNames.length) (h13 : st.regs 13 = newNames.length)
    (hTag : st.regs 7 = 0) (hw : 1 < 2 ^ w)
    (hRoom : st.regs 6 + 2 * (oldNames.length + newNames.length) < 2 ^ w)
    (hCount : st.regs 18 + oldNames.length + newNames.length < 2 ^ w) :
    ∃ out cost edits, Runs w p ω treeEditPackBoth st .normal out cost ∧
      cost ≤ 41 * (oldE.card + newE.card) + 17 ∧ TreeEditDifference oldE newE edits ∧
      TreeEditsAt out.mem (st.regs 6) edits ∧
      out.regs 6 = st.regs 6 + 2 * edits.length ∧ out.regs 18 = st.regs 18 + edits.length ∧
      (∀ r, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 18 →
        out.regs r = st.regs r) ∧
      ∀ a, a < st.regs 6 ∨ st.regs 6 + 2 * edits.length ≤ a → out.mem a = st.mem a := by
  let deleted := oldNames.filter fun e => decide (e ∉ newE)
  let inserted := newNames.filter fun e => decide (e ∉ oldE)
  let edits := deleted.map Chain.TreeChange.delete ++ inserted.map Chain.TreeChange.insert
  have hdiff : TreeEditDifference oldE newE edits := treeEditDifference_of_filter ho hn
  obtain ⟨out, c, hr, hc, h6, h18, hat, hregs, hf⟩ :=
    treeEditPackBoth_runs (p := p) (ω := ω) oldNames newNames _ _ hOld hNew h10 h13 hTag hw hRoom hCount
  have hwords :
      treeEditPackWords 0 (fun e => decide (e ∉ newE)) oldNames ++
        treeEditPackWords 1 (fun e => decide (e ∉ oldE)) newNames = edits.flatMap treeEditWords := by
    simp [edits, deleted, inserted, treeEditPackWords, List.flatMap_map, treeEditWords]
  rw [hwords, treeEditWords_length] at h6 hf
  have hc' : c ≤ 41 * (oldE.card + newE.card) + 17 := by simpa [ho.length_eq, hn.length_eq] using hc
  refine ⟨out, c, edits, hr, hc', hdiff, ?_, h6, ?_, hregs, hf⟩
  · rw [hwords] at hat
    exact hat
  · simpa [edits, deleted, inserted, Nat.add_assoc] using h18

open DynSpanner.Program

/-- The live edge list and presence table are within the dynamic
graph allocation. Together they supply one scan input. -/
private theorem treeEditPackSource_of_graph {w : ℕ} {mem : ℕ → ℕ}
    {base opposite vc vc' ec lo hi : ℕ} {G H : MGraph}
    (hg : DynGraphAt mem base vc ec G) (hh : DynGraphAt mem opposite vc' ec H)
    (hroom : base + dynGraphSize vc ec < 2 ^ w)
    (hroom' : opposite + dynGraphSize vc' ec < 2 ^ w)
    (hsep : ∀ a, base ≤ a → a < base + dynGraphSize vc ec → a < lo ∨ hi ≤ a)
    (hsep' : ∀ a, opposite ≤ a → a < opposite + dynGraphSize vc' ec → a < lo ∨ hi ≤ a) :
    ∃ edges : List ℕ, edges.Perm G.E.toList ∧
      TreeEditPackSource w mem (dgEListBase base vc ec) (dgEPresBase opposite vc') lo hi
        edges (fun e => decide (e ∉ H.E)) := by
  obtain ⟨_, _, hecap, _, _, _, _, _, _, _, _, _, ⟨edges, hlen, hnd, hmem, hlist, _⟩, _, _⟩ := hg
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hpres, _, _, _⟩ := hh
  have hp : edges.Perm G.E.toList := by
    apply List.perm_of_nodup_nodup_toFinset_eq hnd (Finset.nodup_toList _)
    ext e
    simp [hmem e]
  have hsz : edges.length ≤ ec := by
    have hsub : G.E ⊆ Finset.range ec := fun e he => Finset.mem_range.mpr (hecap e he)
    rw [hlen]
    simpa [MGraph.m] using Finset.card_le_card hsub
  refine ⟨edges, hp, ⟨hlist, ?_, ?_, ?_⟩⟩
  · simp only [dgEListBase, dynGraphSize] at hroom ⊢
    omega
  · intro a hlo hhi
    apply hsep a
    · simp only [dgEListBase] at hlo
      omega
    · simp only [dgEListBase, dynGraphSize] at hhi ⊢
      omega
  · intro e he
    have hcap := hecap e ((hmem e).mp he)
    have ha : dgEPresBase opposite vc' + e < opposite + dynGraphSize vc' ec := by
      simp only [dgEPresBase, dynGraphSize]
      omega
    refine ⟨ha.trans hroom', ?_, hsep' _ ?_ ha⟩
    · rw [hpres e hcap]
      by_cases h : e ∈ H.E <;> simp [h]
    · simp only [dgEPresBase]
      omega

/-- Scan the two rebuilt graph allocations using the shared presence and
live edge arrays. The scans emit a buffer accepted by the tree fold. -/
theorem treeEditPackBoth_graphs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {oldBase newBase oldVC newVC ec : ℕ} {G H : MGraph}
    (hold : DynGraphAt st.mem oldBase oldVC ec G)
    (hnew : DynGraphAt st.mem newBase newVC ec H)
    (holdRoom : oldBase + dynGraphSize oldVC ec < 2 ^ w)
    (hnewRoom : newBase + dynGraphSize newVC ec < 2 ^ w)
    (hOldSep : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize oldVC ec →
      a < st.regs 6 ∨ st.regs 6 + 2 * (G.m + H.m) ≤ a)
    (hNewSep : ∀ a, newBase ≤ a → a < newBase + dynGraphSize newVC ec →
      a < st.regs 6 ∨ st.regs 6 + 2 * (G.m + H.m) ≤ a)
    (h7 : st.regs 7 = 0) (h9 : st.regs 9 = dgEPresBase newBase newVC)
    (h10 : st.regs 10 = dgEListBase oldBase oldVC ec) (h11 : st.regs 11 = G.m)
    (h12 : st.regs 12 = dgEListBase newBase newVC ec) (h13 : st.regs 13 = H.m)
    (h14 : st.regs 14 = dgEPresBase oldBase oldVC)
    (hw : 1 < 2 ^ w)
    (hRoom : st.regs 6 + 2 * (G.m + H.m) < 2 ^ w)
    (hCount : st.regs 18 + G.m + H.m < 2 ^ w) :
    ∃ out cost edits, Runs w p ω treeEditPackBoth st .normal out cost ∧
      cost ≤ 41 * (G.m + H.m) + 17 ∧ TreeEditDifference G.E H.E edits ∧
      TreeEditsAt out.mem (st.regs 6) edits ∧
      out.regs 6 = st.regs 6 + 2 * edits.length ∧ out.regs 18 = st.regs 18 + edits.length ∧
      (∀ r, r ≠ 6 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 18 →
        out.regs r = st.regs r) ∧
      ∀ a, a < st.regs 6 ∨ st.regs 6 + 2 * edits.length ≤ a → out.mem a = st.mem a := by
  obtain ⟨oldNames, ho, hOld⟩ := treeEditPackSource_of_graph hold hnew holdRoom hnewRoom hOldSep hNewSep
  obtain ⟨newNames, hn, hNew⟩ := treeEditPackSource_of_graph hnew hold hnewRoom holdRoom hNewSep hOldSep
  have hOldLen : oldNames.length = G.m := by simpa [MGraph.m] using ho.length_eq
  have hNewLen : newNames.length = H.m := by simpa [MGraph.m] using hn.length_eq
  exact treeEditPackBoth_difference ho hn
    (by rw [h10, h9, hOldLen, hNewLen]; exact hOld)
    (by rw [h12, h14, hOldLen, hNewLen]; exact hNew)
    (h11.trans hOldLen.symm) (h13.trans hNewLen.symm) h7 hw
    (by rwa [hOldLen, hNewLen]) (by rwa [hOldLen, hNewLen])

/-- Save the start of the packed edit buffer in register 23, then
restore it to register 6 for the Cut and Link loop. -/
@[expose] def treeEditPackForFold : Stmt :=
  .assign 23 (.reg 6) ;; treeEditPackBoth ;; .assign 6 (.reg 23)

/-- Preparing and restoring the edit cursor adds six steps to packing. -/
theorem treeEditPackForFold_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st mid : State}
    {cost : ℕ} {edits : List Chain.TreeChange}
    (hpack : Runs w p ω treeEditPackBoth
      { st with regs := Function.update st.regs 23 (st.regs 6) } .normal mid cost)
    (hsaved : mid.regs 23 = st.regs 6)
    (hwords : TreeEditsAt mid.mem (st.regs 6) edits) :
    ∃ out, Runs w p ω treeEditPackForFold st .normal out (cost + 6) ∧
      TreeEditsAt out.mem (out.regs 6) edits ∧ out.regs 6 = st.regs 6 ∧ out.mem = mid.mem ∧
      (∀ r, r ≠ 6 → out.regs r = mid.regs r) := by
  let saved := { st with regs := Function.update st.regs 23 (st.regs 6) }
  let out := { mid with regs := Function.update mid.regs 6 (st.regs 6) }
  have hsave : Runs w p ω (.assign 23 (.reg 6)) st .normal saved 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hrestore : Runs w p ω (.assign 6 (.reg 23)) mid .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hsaved], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨saved, 2, cost + 3, hsave,
    runs_seq_iff.mpr (Or.inr ⟨mid, cost, 2, hpack, hrestore, rfl⟩), by omega⟩),
    ?_, by simp [out], rfl, ?_⟩
  · simpa [out] using hwords
  · intro r hr
    exact Function.update_of_ne hr _ _

/-- Pack both graph differences and leave the cursor at the first
edit record. The packed count is left in register 18. -/
theorem treeEditPackForFold_graphs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {oldBase newBase oldVC newVC ec : ℕ} {G H : MGraph}
    (hold : DynGraphAt st.mem oldBase oldVC ec G)
    (hnew : DynGraphAt st.mem newBase newVC ec H)
    (holdRoom : oldBase + dynGraphSize oldVC ec < 2 ^ w)
    (hnewRoom : newBase + dynGraphSize newVC ec < 2 ^ w)
    (hOldSep : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize oldVC ec →
      a < st.regs 6 ∨ st.regs 6 + 2 * (G.m + H.m) ≤ a)
    (hNewSep : ∀ a, newBase ≤ a → a < newBase + dynGraphSize newVC ec →
      a < st.regs 6 ∨ st.regs 6 + 2 * (G.m + H.m) ≤ a)
    (h7 : st.regs 7 = 0) (h9 : st.regs 9 = dgEPresBase newBase newVC)
    (h10 : st.regs 10 = dgEListBase oldBase oldVC ec) (h11 : st.regs 11 = G.m)
    (h12 : st.regs 12 = dgEListBase newBase newVC ec) (h13 : st.regs 13 = H.m)
    (h14 : st.regs 14 = dgEPresBase oldBase oldVC)
    (hw : 1 < 2 ^ w)
    (hRoom : st.regs 6 + 2 * (G.m + H.m) < 2 ^ w)
    (hCount : st.regs 18 + G.m + H.m < 2 ^ w) :
    ∃ out cost edits, Runs w p ω treeEditPackForFold st .normal out cost ∧
      cost ≤ 41 * (G.m + H.m) + 23 ∧ TreeEditDifference G.E H.E edits ∧
      TreeEditsAt out.mem (out.regs 6) edits ∧
      out.regs 6 = st.regs 6 ∧ out.regs 18 = st.regs 18 + edits.length ∧
      (∀ r, r ≠ 23 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 18 →
        out.regs r = st.regs r) ∧
      ∀ a, a < st.regs 6 ∨ st.regs 6 + 2 * edits.length ≤ a → out.mem a = st.mem a := by
  let saved := { st with regs := Function.update st.regs 23 (st.regs 6) }
  obtain ⟨mid, cost, edits, hr, hc, hd, hat, _, hn, hrgs, hf⟩ :=
    treeEditPackBoth_graphs (st := saved) (ω := ω) hold hnew holdRoom hnewRoom
      hOldSep hNewSep (by simpa [saved] using h7) (by simpa [saved] using h9)
      (by simpa [saved] using h10) (by simpa [saved] using h11) (by simpa [saved] using h12)
      (by simpa [saved] using h13) (by simpa [saved] using h14) hw hRoom hCount
  have h23 : mid.regs 23 = st.regs 6 :=
    (hrgs 23 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide)).trans (by simp [saved])
  obtain ⟨out, hrun, hout, h6, hm, hreg⟩ := treeEditPackForFold_runs hr h23 hat
  refine ⟨out, cost + 6, edits, hrun, by omega, hd, hout, h6,
    (hreg 18 (by decide)).trans hn, ?_, ?_⟩
  · intro r h23' h7' h8' h9' h10' h11' h18'
    by_cases h6' : r = 6
    · exact h6' ▸ h6
    · exact (hreg r h6').trans ((hrgs r h6' h7' h8' h9' h10' h11' h18').trans
        (Function.update_of_ne h23' _ _))
  · intro a ha
    rw [hm]
    exact hf a ha

/-- Packing uses registers 12 through 14 for its second scan.
After packing, install the old endpoint table bases from registers
24 through 26 for the Cut and Link loop. -/
@[expose] def treeEditPackInstallOld : Stmt :=
  .assign 12 (.reg 24) ;;
  .assign 13 (.reg 25) ;;
  .assign 14 (.reg 26)

/-- Installing the endpoint bases leaves the buffer and all other
registers intact and costs eight steps. -/
theorem treeEditPackInstallOld_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} (st : State) :
    ∃ out, Runs w p ω treeEditPackInstallOld st .normal out 8 ∧
      out.regs 12 = st.regs 24 ∧ out.regs 13 = st.regs 25 ∧ out.regs 14 = st.regs 26 ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 12 → r ≠ 13 → r ≠ 14 → out.regs r = st.regs r) := by
  let a := { st with regs := Function.update st.regs 12 (st.regs 24) }
  let b := { a with regs := Function.update a.regs 13 (st.regs 25) }
  let out := { b with regs := Function.update b.regs 14 (st.regs 26) }
  have ha : Runs w p ω (.assign 12 (.reg 24)) st .normal a 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hb : Runs w p ω (.assign 13 (.reg 25)) a .normal b 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a, Function.update_of_ne], rfl, rfl, rfl⟩
  have hc : Runs w p ω (.assign 14 (.reg 26)) b .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, a, b, Function.update_of_ne], rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨a, 2, 5, ha,
    runs_seq_iff.mpr (Or.inr ⟨b, 2, 2, hb, hc, rfl⟩), rfl⟩),
    by simp [out, b, a, Function.update_of_ne],
    by simp [out, b, Function.update_of_ne], by simp [out], rfl, ?_⟩
  intro r h12 h13 h14
  simp [out, b, a, Function.update_of_ne, h12, h13, h14]

/-- Produce the packed changes and install the old graph’s endpoint
bases before the edit loop. -/
@[expose] def treeEditPackPrepare : Stmt :=
  treeEditPackForFold ;; treeEditPackInstallOld

/-- The prepared buffer has the exact forest difference, and the
old endpoint register setup adds nine steps to packing. -/
theorem treeEditPackPrepare_graphs {w : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    {oldBase newBase oldVC newVC ec : ℕ} {G H : MGraph}
    (hold : DynGraphAt st.mem oldBase oldVC ec G)
    (hnew : DynGraphAt st.mem newBase newVC ec H)
    (holdRoom : oldBase + dynGraphSize oldVC ec < 2 ^ w)
    (hnewRoom : newBase + dynGraphSize newVC ec < 2 ^ w)
    (hOldSep : ∀ a, oldBase ≤ a → a < oldBase + dynGraphSize oldVC ec →
      a < st.regs 6 ∨ st.regs 6 + 2 * (G.m + H.m) ≤ a)
    (hNewSep : ∀ a, newBase ≤ a → a < newBase + dynGraphSize newVC ec →
      a < st.regs 6 ∨ st.regs 6 + 2 * (G.m + H.m) ≤ a)
    (h7 : st.regs 7 = 0) (h9 : st.regs 9 = dgEPresBase newBase newVC)
    (h10 : st.regs 10 = dgEListBase oldBase oldVC ec) (h11 : st.regs 11 = G.m)
    (h12 : st.regs 12 = dgEListBase newBase newVC ec) (h13 : st.regs 13 = H.m)
    (h14 : st.regs 14 = dgEPresBase oldBase oldVC)
    (h24 : st.regs 24 = dgETailSlotBase oldBase oldVC ec)
    (h25 : st.regs 25 = dgEHeadSlotBase oldBase oldVC ec)
    (h26 : st.regs 26 = dgIntToExtBase oldBase oldVC)
    (hw : 1 < 2 ^ w)
    (hRoom : st.regs 6 + 2 * (G.m + H.m) < 2 ^ w)
    (hCount : st.regs 18 + G.m + H.m < 2 ^ w) :
    ∃ out cost edits, Runs w p ω treeEditPackPrepare st .normal out cost ∧
      cost ≤ 41 * (G.m + H.m) + 32 ∧ TreeEditDifference G.E H.E edits ∧
      TreeEditsAt out.mem (out.regs 6) edits ∧
      out.regs 6 = st.regs 6 ∧ out.regs 18 = st.regs 18 + edits.length ∧
      out.regs 12 = dgETailSlotBase oldBase oldVC ec ∧
      out.regs 13 = dgEHeadSlotBase oldBase oldVC ec ∧
      out.regs 14 = dgIntToExtBase oldBase oldVC ∧
      (∀ r, r ≠ 12 → r ≠ 13 → r ≠ 14 → r ≠ 23 → r ≠ 7 → r ≠ 8 → r ≠ 9 → r ≠ 10 → r ≠ 11 → r ≠ 18 →
        out.regs r = st.regs r) ∧
      ∀ a, a < st.regs 6 ∨ st.regs 6 + 2 * edits.length ≤ a → out.mem a = st.mem a := by
  obtain ⟨mid, cost, edits, hr, hc, hd, hat, h6, h18, hrgs, hf⟩ :=
    treeEditPackForFold_graphs (ω := ω) hold hnew holdRoom hnewRoom hOldSep hNewSep
      h7 h9 h10 h11 h12 h13 h14 hw hRoom hCount
  obtain ⟨out, hi, hout12, hout13, hout14, hm, hreg⟩ :=
    treeEditPackInstallOld_runs (w := w) (p := p) (ω := ω) mid
  have hr6 := (hreg 6 (by decide) (by decide) (by decide)).trans h6
  refine ⟨out, cost + 9, edits, runs_seq_iff.mpr (Or.inr ⟨mid, cost, 8, hr, hi, by omega⟩),
    by omega, hd, ?_, hr6, (hreg 18 (by decide) (by decide) (by decide)).trans h18,
    hout12.trans ((hrgs 24 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h24),
    hout13.trans ((hrgs 25 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h25),
    hout14.trans ((hrgs 26 (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)).trans h26), ?_, ?_⟩
  · rw [hm, hr6, ← h6]
    exact hat
  · intro r h12 h13 h14 h23 h7 h8 h9 h10 h11 h18
    exact (hreg r h12 h13 h14).trans (hrgs r h23 h7 h8 h9 h10 h11 h18)
  · intro a ha
    rw [hm]
    exact hf a ha

end MinCostFlow.MinRatio
