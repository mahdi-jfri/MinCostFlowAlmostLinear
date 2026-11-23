module

public import MinCostFlow.MinRatio.SolverRep
public import WordRAM.CopyWords
import WordRAM.Tactic

/-!
# Dynamic internal-table growth helpers for `Update`

Defines `growIntTablesCopy`, `growIntTablesPatch`, and `growIntTablesBody`, together with
the sub-step specifications (`fillInverseTail_runs`, `copyOneTable_runs`,
`growIntTablesPatch_runs`) and `solverStateRep_after_grow`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Copy the six `intCap`-indexed arrays (`reg 5 = intCap`) from `SolverRootDirAt` (`reg 0`)
into `reg 8 .. reg 13` and fill `newInverse[intCap .. newCap)` (`reg 7 = newCap`) with identity. -/
@[expose] def growIntTablesCopy (copyWords : ℕ) : Stmt :=
  (.assign 15 (.load (.bin .add (.reg 0) (.const 4))) ;;
   .call 16 copyWords [.reg 15, .reg 8, .reg 5]) ;;
  forRange 15 (.reg 5) (.reg 7) (.store (.bin .add (.reg 8) (.reg 15)) (.reg 15)) ;;
  (.assign 15 (.load (.bin .add (.reg 0) (.const 6))) ;;
   .call 16 copyWords [.reg 15, .reg 9, .reg 5]) ;;
  (.assign 15 (.load (.bin .add (.reg 0) (.const 9))) ;;
   .call 16 copyWords [.reg 15, .reg 10, .reg 5]) ;;
  (.assign 15 (.load (.bin .add (.reg 0) (.const 10))) ;;
   .call 16 copyWords [.reg 15, .reg 11, .reg 5]) ;;
  (.assign 15 (.load (.bin .add (.reg 0) (.const 12))) ;;
   .call 16 copyWords [.reg 15, .reg 12, .reg 5]) ;;
  (.assign 15 (.load (.bin .add (.reg 0) (.const 13))) ;;
   .call 16 copyWords [.reg 15, .reg 13, .reg 5])

/-- Patch `SolverRootDirAt` (`root + 4, 6, 9, 10, 12, 13, 15`) and `DetectHeaderAt`
(`handle + 2 := newInverse`) after table reallocation. -/
@[expose] def growIntTablesPatch : Stmt :=
  .store (.bin .add (.reg 0) (.const 4)) (.reg 8) ;;
  .store (.bin .add (.reg 0) (.const 6)) (.reg 9) ;;
  .store (.bin .add (.reg 0) (.const 9)) (.reg 10) ;;
  .store (.bin .add (.reg 0) (.const 10)) (.reg 11) ;;
  .store (.bin .add (.reg 0) (.const 12)) (.reg 12) ;;
  .store (.bin .add (.reg 0) (.const 13)) (.reg 13) ;;
  .store (.bin .add (.reg 0) (.const 15)) (.reg 7) ;;
  .assign 15 (.load (.reg 0)) ;;
  .store (.bin .add (.reg 15) (.const 2)) (.reg 8)

/-- Allocate six `newCap`-sized arrays (`reg 7 = newCap`) starting at `reg 8 = heap`
(with `reg 0 = root`, `reg 5 = intCap`), copy the old `intCap`-indexed tables, fill the inverse
tail with identity, and patch `SolverRootDirAt` and `DetectHeaderAt`, leaving `heap + 6 * newCap`
in `reg 14`. -/
@[expose] def growIntTablesFromReg7 (copyWords : ℕ) : Stmt :=
  .assign 9 (.bin .add (.reg 8) (.reg 7)) ;;
  .assign 10 (.bin .add (.reg 9) (.reg 7)) ;;
  .assign 11 (.bin .add (.reg 10) (.reg 7)) ;;
  .assign 12 (.bin .add (.reg 11) (.reg 7)) ;;
  .assign 13 (.bin .add (.reg 12) (.reg 7)) ;;
  .assign 14 (.bin .add (.reg 13) (.reg 7)) ;;
  growIntTablesCopy copyWords ;;
  growIntTablesPatch

theorem growIntTablesFromReg7_noRand (copyWords : ℕ) :
    (growIntTablesFromReg7 copyWords).NoRand := by
  simp [growIntTablesFromReg7, growIntTablesCopy, growIntTablesPatch, forRange, forUp, Stmt.NoRand]

/-- Fixed deterministic dynamic-table growth entry taking `[root, batchLen, heap]`.
If `intCap < nextFresh + batchLen`, reallocates all six `intCap`-indexed tables to
`newCap = 2 * (nextFresh + batchLen)` at `[heap, heap + 6 * newCap)` and returns
`heap + 6 * newCap`; otherwise returns `heap` without modifying memory. -/
@[expose] def growIntTablesBody (copyWords : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const 5))) ;;
  .assign 4 (.load (.reg 3)) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 15))) ;;
  .assign 6 (.bin .add (.reg 4) (.reg 1)) ;;
  .cond (.bin .lt (.reg 5) (.reg 6))
    (.assign 7 (.bin .mul (.const 2) (.reg 6)) ;;
     .assign 8 (.reg 2) ;;
     growIntTablesFromReg7 copyWords ;;
     .ret (.reg 14))
    (.ret (.reg 2))

theorem growIntTablesBody_noRand (copyWords : ℕ) : (growIntTablesBody copyWords).NoRand := by
  simp [growIntTablesBody, growIntTablesFromReg7_noRand, Stmt.NoRand]

/-- Helper: `translateBatch` preserves `∀ j ≥ nextFresh, intToExt j = j`. -/
theorem translateBatch_intToExt_id_above :
    ∀ (U : List Update) (G : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ),
      (∀ j ≥ nf, i2e j = j) →
      let res := translateBatch G e2i i2e nf U
      ∀ j ≥ res.2.2.2.1, res.2.2.1 j = j
  | [], _, _, _, _, hid => hid
  | u :: rest, G, e2i, i2e, nf, hid => by
    dsimp only [translateBatch]
    cases u with
    | delete e =>
      exact translateBatch_intToExt_id_above rest _ e2i i2e nf hid
    | insert e a b =>
      refine translateBatch_intToExt_id_above rest _ _ _ (nf + 1) ?_
      intro j hj
      dsimp only [translateUpdate]
      rw [Function.update_of_ne (by omega)]
      exact hid j (by omega)
    | split v v' St Sh =>
      exact translateBatch_intToExt_id_above rest _ e2i i2e nf hid

/-- `translateBatch` hands out at most one fresh name per update, and never takes one back:
the counter moves from `nf` to a value in `[nf, nf + U.length]`. -/
theorem translateBatch_nextFresh_bounds :
    ∀ (U : List Update) (G : MGraph) (e2i i2e : ℕ → ℕ) (nf : ℕ),
      nf ≤ (translateBatch G e2i i2e nf U).2.2.2.1 ∧
        (translateBatch G e2i i2e nf U).2.2.2.1 ≤ nf + U.length
  | [], _, _, _, _ => ⟨le_rfl, by simp [translateBatch]⟩
  | u :: rest, G, e2i, i2e, nf => by
    cases u with
    | delete e =>
      have h := translateBatch_nextFresh_bounds rest (G.applyUpdate (.delete e)) e2i i2e nf
      dsimp only [translateBatch, translateUpdate]; simp only [List.length_cons]
      exact ⟨h.1, le_trans h.2 (by omega)⟩
    | insert e a b =>
      have h := translateBatch_nextFresh_bounds rest (G.applyUpdate (.insert e a b))
        (Function.update e2i e nf) (Function.update i2e nf e) (nf + 1)
      dsimp only [translateBatch, translateUpdate]; simp only [List.length_cons]
      exact ⟨le_trans (Nat.le_succ nf) h.1, le_trans h.2 (by omega)⟩
    | split v v' St Sh =>
      have h := translateBatch_nextFresh_bounds rest (G.applyUpdate (.split v v' St Sh)) e2i i2e nf
      dsimp only [translateBatch, translateUpdate]; simp only [List.length_cons]
      exact ⟨h.1, le_trans h.2 (by omega)⟩

/-- Filling `newInverse[lo .. hi)` with identity via `forRange 15`. -/
theorem fillInverseTail_runs {w base lo hi : ℕ} {p : Program} {ω : ℕ → Bool} {st : State}
    (hloHi : lo ≤ hi) (hr5 : st.regs 5 = lo) (hr7 : st.regs 7 = hi) (hr8 : st.regs 8 = base)
    (hw1 : 1 < 2 ^ w) (hroom : base + hi < 2 ^ w) :
    ∃ out c,
      Runs w p ω (forRange 15 (.reg 5) (.reg 7) (.store (.bin .add (.reg 8) (.reg 15)) (.reg 15)))
        st .normal out c ∧
      c ≤ 17 * (hi - lo) + 12 ∧
      (∀ r ≤ 14, out.regs r = st.regs r) ∧
      (∀ j, lo ≤ j → j < hi → out.mem (base + j) = j) ∧
      (∀ a, a < base + lo ∨ base + hi ≤ a → out.mem a = st.mem a) := by
  have hloop := Triple.forRange_const (p := p) (r := 15) (lo := .reg 5) (hi := .reg 7)
    (body := .store (.bin .add (.reg 8) (.reg 15)) (.reg 15))
    (P := fun s => s = st)
    (Inv := fun k s =>
      (∀ r ≤ 14, s.regs r = st.regs r) ∧ s.regs 15 = k ∧
      (∀ j, lo ≤ j → j < k → s.mem (base + j) = j) ∧
      (∀ a, a < base + lo ∨ base + k ≤ a → s.mem a = st.mem a))
    5 lo hi hloHi hw1 (fun _ => by omega)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, hr5], fun r hr => by simp [Function.update_of_ne (show r ≠ 15 by omega)],
        by simp, fun _ h1 h2 => by omega, fun _ _ => rfl⟩)
    (fun _ _ _ _ hI => hI.2.1)
    (fun _ s _ _ hI => by simp [Expr.eval, hI.1 7 (by decide), hr7])
    (fun j hloJ hjHi => by
      intro s ω ⟨hregs, hr15, hfilled, hfr⟩
      let s' : State := { s with mem := Function.update s.mem (base + j) j }
      refine ⟨.normal, s', 5, runs_store_iff.mpr ⟨base + j, j,
        by simp [Expr.eval, BinOp.eval, hregs 8 (by decide), hr8, hr15, show base + j < 2 ^ w by omega],
        by simp [Expr.eval, hr15], rfl, rfl, rfl⟩, ?_, le_rfl⟩
      refine ⟨⟨fun r hr => by simp [s', Function.update_of_ne (show r ≠ 15 by omega), hregs r hr],
        by simp [s'], ?_, ?_⟩, hr15⟩
      · intro x hx1 hx2
        by_cases hxj : x = j
        · subst hxj; simp [s']
        · simp only [s', Function.update_of_ne (show base + x ≠ base + j by omega)]
          exact hfilled x hx1 (by omega)
      · intro a ha
        simp only [s', Function.update_of_ne (show a ≠ base + j by omega)]
        exact hfr a (by omega))
  obtain ⟨o, out, c, hr, hpost, hc⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hpost
  | normal =>
    refine ⟨out, c, hr, ?_, hpost.1, hpost.2.2.1, hpost.2.2.2⟩
    simp only [Expr.size] at hc
    have hmul : (hi - lo) * (5 + 1 + 8) ≤ 17 * (hi - lo) := by omega
    omega

/-- One `assign 15 (load (root + off)) ;; call 16 copyWords [reg 15, reg dstR, reg 5]`
step copying `intCap` words from `oldPtr` to `dst`. -/
theorem copyOneTable_runs {w copyWords root off dstR oldPtr dst intCap : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hCopy : MeetsContract w p copyWords (copyWordsContract w))
    (hr0 : st.regs 0 = root) (hr5 : st.regs 5 = intCap) (hrDst : st.regs dstR = dst)
    (hdstLe14 : dstR ≤ 14)
    (hoffW : off < 2 ^ w) (hrootOffW : root + off < 2 ^ w)
    (hmPtr : st.mem (root + off) = oldPtr)
    (hw1 : 1 < 2 ^ w) (holdEnd : oldPtr + intCap ≤ dst) (hdstEnd : dst + intCap < 2 ^ w) :
    ∃ out c,
      Runs w p ω
        (.assign 15 (.load (.bin .add (.reg 0) (.const off))) ;;
         .call 16 copyWords [.reg 15, .reg dstR, .reg 5])
        st .normal out c ∧
      c ≤ 17 * intCap + 20 ∧
      (∀ r ≤ 14, out.regs r = st.regs r) ∧
      (∀ i < intCap, out.mem (dst + i) = st.mem (oldPtr + i)) ∧
      (∀ a, a < dst ∨ dst + intCap ≤ a → out.mem a = st.mem a) := by
  let s1 : State := { st with regs := Function.update st.regs 15 oldPtr }
  have r1 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 0) (.const off)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨oldPtr, by simp [Expr.eval, BinOp.eval, hr0, hoffW, hrootOffW, hmPtr],
      rfl, rfl, rfl⟩
  obtain ⟨bodyC, hbodyC, oC, stC, cC, hrC, ⟨_, _, _, hargsC, _, hcopied, hfrC⟩, hcC⟩ :=
    hCopy [oldPtr, dst, intCap] s1.mem s1.pos ω
      (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
          rcases hx with rfl | rfl | rfl <;> omega)
      ⟨oldPtr, dst, intCap, rfl, hw1, by omega, by omega, Or.inr holdEnd⟩
  simp only [List.cons.injEq, and_true] at hargsC
  rcases hargsC with ⟨rfl, rfl, rfl⟩
  change cC ≤ 17 * intCap + 10 at hcC
  let out : State := { regs := Function.update s1.regs 16 oC.value, mem := stC.mem, pos := stC.pos }
  have r2 : Runs w p ω (.call 16 copyWords [.reg 15, .reg dstR, .reg 5]) s1 .normal out (cC + 4) :=
    runs_call_iff.mpr ⟨[oldPtr, dst, intCap], bodyC, oC, stC, cC,
      by simp [evalArgs, Expr.eval, s1, Function.update_of_ne (show dstR ≠ 15 by omega), hrDst, hr5],
      hbodyC, hrC, rfl, rfl, by simp [argsSize, Expr.size]; omega⟩
  refine ⟨out, 5 + (cC + 4) + 1, runs_seq_iff.mpr (Or.inr ⟨s1, 5, cC + 4, r1, r2, rfl⟩),
    by omega, fun r hr => by
      simp [out, s1, Function.update_of_ne (show r ≠ 16 by omega),
        Function.update_of_ne (show r ≠ 15 by omega)],
    hcopied, hfrC⟩

/-- Executing `growIntTablesPatch` updates the 7 `SolverRootDirAt` fields and `handle + 2`
in 51 steps, leaving all other memory unchanged. -/
theorem growIntTablesPatch_runs
    {w root handle newCap newInv newSl newET newER newOL newIO : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (hr0 : st.regs 0 = root) (hr7 : st.regs 7 = newCap) (hr8 : st.regs 8 = newInv)
    (hr9 : st.regs 9 = newSl) (hr10 : st.regs 10 = newET) (hr11 : st.regs 11 = newER)
    (hr12 : st.regs 12 = newOL) (hr13 : st.regs 13 = newIO)
    (hm0 : st.mem root = handle) (hrootNe : ∀ j < 16, j ≠ 0 → root + j ≠ root)
    (hw15 : 15 < 2 ^ w) (hroot15W : root + 15 < 2 ^ w) (hh2W : handle + 2 < 2 ^ w)
    (hhNeRoot : ∀ j < 16, handle + 2 ≠ root + j) :
    ∃ out,
      Runs w p ω growIntTablesPatch st .normal out 51 ∧
      (∀ r ≤ 14, out.regs r = st.regs r) ∧
      out.mem (root + 4) = newInv ∧ out.mem (root + 6) = newSl ∧
      out.mem (root + 9) = newET ∧ out.mem (root + 10) = newER ∧
      out.mem (root + 12) = newOL ∧ out.mem (root + 13) = newIO ∧
      out.mem (root + 15) = newCap ∧ out.mem (handle + 2) = newInv ∧
      (∀ a, a ≠ root + 4 → a ≠ root + 6 → a ≠ root + 9 → a ≠ root + 10 →
        a ≠ root + 12 → a ≠ root + 13 → a ≠ root + 15 → a ≠ handle + 2 →
        out.mem a = st.mem a) := by
  let s1 := { st with mem := Function.update st.mem (root + 4) newInv }
  let s2 := { s1 with mem := Function.update s1.mem (root + 6) newSl }
  let s3 := { s2 with mem := Function.update s2.mem (root + 9) newET }
  let s4 := { s3 with mem := Function.update s3.mem (root + 10) newER }
  let s5 := { s4 with mem := Function.update s4.mem (root + 12) newOL }
  let s6 := { s5 with mem := Function.update s5.mem (root + 13) newIO }
  let s7 := { s6 with mem := Function.update s6.mem (root + 15) newCap }
  let s8 := { s7 with regs := Function.update s7.regs 15 handle }
  let s9 := { s8 with mem := Function.update s8.mem (handle + 2) newInv }
  have hst (s : State) (off r v : ℕ) (ho : off ≤ 15) (h0 : s.regs 0 = root) (hv : s.regs r = v) :
      Runs w p ω (.store (.bin .add (.reg 0) (.const off)) (.reg r)) s .normal
        { s with mem := Function.update s.mem (root + off) v } 5 :=
    runs_store_iff.mpr ⟨root + off, v,
      by simp [Expr.eval, BinOp.eval, h0, show off < 2 ^ w by omega, show root + off < 2 ^ w by omega],
      by simp [Expr.eval, hv], rfl, rfl, rfl⟩
  have r1 := hst st 4 8 newInv (by decide) hr0 hr8
  have r2 := hst s1 6 9 newSl (by decide) hr0 hr9
  have r3 := hst s2 9 10 newET (by decide) hr0 hr10
  have r4 := hst s3 10 11 newER (by decide) hr0 hr11
  have r5 := hst s4 12 12 newOL (by decide) hr0 hr12
  have r6 := hst s5 13 13 newIO (by decide) hr0 hr13
  have r7 := hst s6 15 7 newCap (by decide) hr0 hr7
  have hm0_7 : s7.mem root = handle := by
    dsimp only [s7, s6, s5, s4, s3, s2, s1]
    rw [Function.update_of_ne (hrootNe 15 (by omega) (by decide)).symm,
      Function.update_of_ne (hrootNe 13 (by omega) (by decide)).symm,
      Function.update_of_ne (hrootNe 12 (by omega) (by decide)).symm,
      Function.update_of_ne (hrootNe 10 (by omega) (by decide)).symm,
      Function.update_of_ne (hrootNe 9 (by omega) (by decide)).symm,
      Function.update_of_ne (hrootNe 6 (by omega) (by decide)).symm,
      Function.update_of_ne (hrootNe 4 (by omega) (by decide)).symm, hm0]
  have r8 : Runs w p ω (.assign 15 (.load (.reg 0))) s7 .normal s8 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, show s7.regs 0 = root from hr0, hm0_7],
      rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.store (.bin .add (.reg 15) (.const 2)) (.reg 8)) s8 .normal s9 5 :=
    runs_store_iff.mpr ⟨handle + 2, newInv,
      by simp [Expr.eval, BinOp.eval, s8, show 2 < 2 ^ w by omega, hh2W],
      by simp [Expr.eval, s8, s7, s6, s5, s4, s3, s2, s1, hr8], rfl, rfl, rfl⟩
  refine ⟨s9,
    runs_seq_iff.mpr (Or.inr ⟨s1, 5, 45, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, 39, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, 33, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, 27, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 5, 21, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 5, 15, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, 5, 9, r7,
      runs_seq_iff.mpr (Or.inr ⟨s8, 3, 5, r8, r9, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩),
    fun r hr => by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne (show r ≠ 15 by omega)],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, Function.update_of_ne (hhNeRoot 4 (by omega)).symm],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, Function.update_of_ne (hhNeRoot 6 (by omega)).symm],
    by simp [s9, s8, s7, s6, s5, s4, s3, Function.update_of_ne (hhNeRoot 9 (by omega)).symm],
    by simp [s9, s8, s7, s6, s5, s4, Function.update_of_ne (hhNeRoot 10 (by omega)).symm],
    by simp [s9, s8, s7, s6, s5, Function.update_of_ne (hhNeRoot 12 (by omega)).symm],
    by simp [s9, s8, s7, s6, Function.update_of_ne (hhNeRoot 13 (by omega)).symm],
    by simp [s9, s8, s7, Function.update_of_ne (hhNeRoot 15 (by omega)).symm],
    by simp [s9],
    fun a h4 h6 h9 h10 h12 h13 h15 hh2 => by
      simp [s9, s8, s7, s6, s5, s4, s3, s2, s1,
        Function.update_of_ne h4, Function.update_of_ne h6, Function.update_of_ne h9,
        Function.update_of_ne h10, Function.update_of_ne h12, Function.update_of_ne h13,
        Function.update_of_ne h15, Function.update_of_ne hh2]⟩

private theorem listAt_congr_grow {mem mem' : ℕ → ℕ} {base : ℕ} {xs : List ℕ}
    (h : ListAt mem base xs) (hag : ∀ j < xs.length, mem' (base + j) = mem (base + j)) :
    ListAt mem' base xs := fun j hj => (hag j hj).trans (h j hj)

/-- Re-establish `solverStateRep` after dynamic table reallocation to `newCap`. -/
theorem solverStateRep_after_grow {cfg : Alg2Config}
    {L P m V psi k epsExp drainUnit : ℕ} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (hlocalCore : Rcore.Local)
    {root heap newCap : ℕ} {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {mem mem' : ℕ → ℕ}
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < heap)
    (hcapLt : tok.intCap < newCap) (hnfLe : model.nextFresh ≤ tok.intCap)
    (hinvLo : ∀ j < tok.intCap, mem' (heap + j) = mem (tok.inverse + j))
    (hinvHi : ∀ j, tok.intCap ≤ j → j < newCap → mem' (heap + j) = j)
    (hslLo : ∀ j < tok.intCap, mem' (heap + newCap + j) = mem (tok.slots + j))
    (hetLo : ∀ j < tok.intCap, mem' (heap + 2 * newCap + j) = mem (tok.edgeThresholds + j))
    (herLo : ∀ j < tok.intCap, mem' (heap + 3 * newCap + j) = mem (tok.edgeRecords + j))
    (holLo : ∀ j < tok.intCap, mem' (heap + 4 * newCap + j) = mem (tok.offReadyList + j))
    (hioLo : ∀ j < tok.intCap, mem' (heap + 5 * newCap + j) = mem (tok.inOffReady + j))
    (hioHi : ∀ j, tok.intCap ≤ j → j < newCap → mem' (heap + 5 * newCap + j) = 0)
    (hroot4 : mem' (root + 4) = heap)
    (hroot6 : mem' (root + 6) = heap + newCap)
    (hroot9 : mem' (root + 9) = heap + 2 * newCap)
    (hroot10 : mem' (root + 10) = heap + 3 * newCap)
    (hroot12 : mem' (root + 12) = heap + 4 * newCap)
    (hroot13 : mem' (root + 13) = heap + 5 * newCap)
    (hroot15 : mem' (root + 15) = newCap)
    (hh2 : mem' (tok.handle + 2) = heap)
    (hframe : ∀ a < heap, a ≠ root + 4 → a ≠ root + 6 → a ≠ root + 9 → a ≠ root + 10 →
      a ≠ root + 12 → a ≠ root + 13 → a ≠ root + 15 → a ≠ tok.handle + 2 → mem' a = mem a) :
    let tok' : SolverToken cfg L Rcore :=
      { tok with
        inverse := heap
        slots := heap + newCap
        edgeThresholds := heap + 2 * newCap
        edgeRecords := heap + 3 * newCap
        offReadyList := heap + 4 * newCap
        inOffReady := heap + 5 * newCap
        intCap := newCap
        owned := fun a => tok.owned a ∨ (heap ≤ a ∧ a < heap + 6 * newCap)
        tag := fun a =>
          if heap ≤ a ∧ a < heap + newCap then 8
          else if heap + newCap ≤ a ∧ a < heap + 2 * newCap then 9
          else if heap + 2 * newCap ≤ a ∧ a < heap + 3 * newCap then 12
          else if heap + 3 * newCap ≤ a ∧ a < heap + 4 * newCap then 13
          else if heap + 4 * newCap ≤ a ∧ a < heap + 5 * newCap then 14
          else if heap + 5 * newCap ≤ a ∧ a < heap + 6 * newCap then 15
          else tok.tag a }
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok' mem' ∧
    (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok' mem' =
      (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).phi root tok mem := by
  dsimp only
  obtain ⟨hrootDir, hdetect, hnum, hchainP, hfreshInv, hfreshTab, hextM, hintCapE,
    hsched, hoffReady, htn, hlct, htrep, hedgeAcc, hcores, htermH, htermBr, htermRep, hwire, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, t12, t13, t14, t15,
    t16, t1718, t19, t20, t21⟩ := htags
  have hltH {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) : a < heap :=
    hbelow a (Or.inl (hOwn a (ht ▸ hv)))
  have hagT {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) (hv1 : v ≠ 1) (hv2 : v ≠ 2) :
      mem' a = mem a :=
    hframe a (hltH ht hv)
      (fun h => hv1 (ht.symm.trans (h ▸ t1 4 (by omega))))
      (fun h => hv1 (ht.symm.trans (h ▸ t1 6 (by omega))))
      (fun h => hv1 (ht.symm.trans (h ▸ t1 9 (by omega))))
      (fun h => hv1 (ht.symm.trans (h ▸ t1 10 (by omega))))
      (fun h => hv1 (ht.symm.trans (h ▸ t1 12 (by omega))))
      (fun h => hv1 (ht.symm.trans (h ▸ t1 13 (by omega))))
      (fun h => hv1 (ht.symm.trans (h ▸ t1 15 (by omega))))
      (fun h => hv2 (ht.symm.trans (h ▸ t2 2 (by omega))))
  have htagKeep {a v : ℕ} (ht : tok.tag a = v) (hv : v ≠ 0) :
      (if heap ≤ a ∧ a < heap + newCap then 8
        else if heap + newCap ≤ a ∧ a < heap + 2 * newCap then 9
        else if heap + 2 * newCap ≤ a ∧ a < heap + 3 * newCap then 12
        else if heap + 3 * newCap ≤ a ∧ a < heap + 4 * newCap then 13
        else if heap + 4 * newCap ≤ a ∧ a < heap + 5 * newCap then 14
        else if heap + 5 * newCap ≤ a ∧ a < heap + 6 * newCap then 15
        else tok.tag a) = v := by
    have hlt := hltH ht hv
    simp only [show ¬ (heap ≤ a ∧ a < heap + newCap) by omega,
      show ¬ (heap + newCap ≤ a ∧ a < heap + 2 * newCap) by omega,
      show ¬ (heap + 2 * newCap ≤ a ∧ a < heap + 3 * newCap) by omega,
      show ¬ (heap + 3 * newCap ≤ a ∧ a < heap + 4 * newCap) by omega,
      show ¬ (heap + 4 * newCap ≤ a ∧ a < heap + 5 * newCap) by omega,
      show ¬ (heap + 5 * newCap ≤ a ∧ a < heap + 6 * newCap) by omega, ↓reduceIte, ht]
  have htreeLocal := LinkCut.PathProg.pathRep_local 4 L LinkCut.PathProg.pathC
  have htree_ag (a : ℕ) (ha : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot
      tok.treeHeap tok.treeTok a) : mem a = mem' a :=
    (hagT (t16 a ha) (by decide) (by decide) (by decide)).symm
  have hcore_ag (i : ℕ) (hi : i < cfg.P.d) (a : ℕ)
      (ha : Rcore.foot (tok.coreHandle i) (tok.coreTok i) a) : mem a = mem' a :=
    (hagT (t21 i hi a ha) (by omega) (by omega) (by omega)).symm
  have htermLocal := LastLevelProgram.lastLevelRepresentation_local tok.vcLast tok.ecLast
    4 L P (model.chain.G cfg.P.d).E
  have hterm_ag (a : ℕ)
      (ha : (LastLevelProgram.lastLevelRepresentation tok.vcLast tok.ecLast 4 L P
        (model.chain.G cfg.P.d).E).foot tok.termHandle tok.termTok a) : mem a = mem' a :=
    (hagT (t19 a ((lastLevelRepresentation_foot_indep_P _ _ _ _ P 0 _ _ _ _).mp ha))
      (by decide) (by decide) (by decide)).symm
  refine ⟨⟨?_, ?_,
    listAt_congr_grow hnum (fun j hj => by
      have h1 : tok.handle + 5 + j = tok.handle + (5 + j) := by omega
      have hneR (k : ℕ) (hk : k < 16) : tok.handle + (5 + j) ≠ root + k := fun h => by
        have ht := t2 (5 + j) (by simp [List.length] at hj; omega); rw [h, t1 k hk] at ht; omega
      rw [h1]
      exact hframe _ (hltH (t2 (5 + j) (by simp [List.length] at hj; omega)) (by decide))
        (hneR 4 (by omega)) (hneR 6 (by omega)) (hneR 9 (by omega)) (hneR 10 (by omega))
        (hneR 12 (by omega)) (hneR 13 (by omega)) (hneR 15 (by omega)) (by omega)),
    listAt_congr_grow hchainP (fun j hj => by
      have h1 : tok.handle + 9 + j = tok.handle + (9 + j) := by omega
      have hneR (k : ℕ) (hk : k < 16) : tok.handle + (9 + j) ≠ root + k := fun h => by
        have ht := t2 (9 + j) (by simp [List.length] at hj; omega); rw [h, t1 k hk] at ht; omega
      rw [h1]
      exact hframe _ (hltH (t2 (9 + j) (by simp [List.length] at hj; omega)) (by decide))
        (hneR 4 (by omega)) (hneR 6 (by omega)) (hneR 9 (by omega)) (hneR 10 (by omega))
        (hneR 12 (by omega)) (hneR 13 (by omega)) (hneR 15 (by omega)) (by omega)),
    hfreshInv, ⟨(hagT t6 (by decide) (by decide) (by decide)).trans hfreshTab.1,
      fun e he => (hagT (t7 e he) (by decide) (by decide) (by decide)).trans (hfreshTab.2.1 e he),
      fun j hj => by
        by_cases hlt : j < tok.intCap
        · exact (hinvLo j hlt).trans (hfreshTab.2.2 j hlt)
        · exact (hinvHi j (by omega) hj).trans (hintCapE.2.2.2 j (by omega)).symm⟩,
    hextM, ⟨fun e he => lt_trans (hintCapE.1 e he) hcapLt, lt_trans hintCapE.2.1 hcapLt, le_trans hintCapE.2.2.1 hcapLt.le,
      fun j hj => hintCapE.2.2.2 j (le_trans hcapLt.le hj)⟩,
    ⟨fun i => (hagT (t5 i.val (by omega)) (by decide) (by decide) (by decide)).trans (hsched.1 i),
      fun i hi => by
        have h1 : tok.levelsEnd + (cfg.P.d + 1) + i = tok.levelsEnd + (cfg.P.d + 1 + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 2 * (cfg.P.d + 1) + i = tok.levelsEnd + (2 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.2.1 i hi),
      fun i hi => by
        have h1 : tok.levelsEnd + 3 * (cfg.P.d + 1) + i = tok.levelsEnd + (3 * (cfg.P.d + 1) + i) := by omega
        rw [h1]; exact (hagT (t5 _ (by omega)) (by decide) (by decide) (by decide)).trans (by rw [← h1]; exact hsched.2.2.2.1 i hi),
      (hagT (t5 (4 * (cfg.P.d + 1)) (by omega)) (by decide) (by decide) (by decide)).trans hsched.2.2.2.2⟩,
    ?_, htn, hlct, (htreeLocal tok.treeHeap tok.tree tok.treeTok mem mem' htree_ag).1 htrep,
    ?_, ?_,
    (hagT (t4 cfg.P.d (by omega)) (by decide) (by decide) (by decide)).trans htermH,
    by
      have h1 : tok.handle + 18 + (cfg.P.d + 1) + cfg.P.d = tok.handle + 18 + (2 * cfg.P.d + 1) := by omega
      rw [h1] at htermBr ⊢; exact (hagT (t4 _ (by omega)) (by decide) (by decide) (by decide)).trans htermBr,
    (htermLocal tok.termHandle _ tok.termTok mem mem' hterm_ag).1 htermRep, ?_, ?_⟩, ?_⟩
  · intro j hj
    have hj16 : j < 16 := by simpa [List.length] using hj
    have hneH : root + j ≠ tok.handle + 2 := fun h => by
      have ht := t1 j hj16; rw [h, t2 2 (by omega)] at ht; omega
    interval_cases j
    · simpa [hframe root (by simpa using hltH (t1 0 (by omega)) (by decide)) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) (by omega) (by simpa using hneH)] using hrootDir 0 (by simp)
    · simpa [hframe _ (hltH (t1 1 (by omega)) (by decide)) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hneH] using hrootDir 1 (by simp)
    · simpa [hframe _ (hltH (t1 2 (by omega)) (by decide)) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hneH] using hrootDir 2 (by simp)
    · simpa [hframe _ (hltH (t1 3 (by omega)) (by decide)) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hneH] using hrootDir 3 (by simp)
    · simpa using hroot4
    · simpa [hframe _ (hltH (t1 5 (by omega)) (by decide)) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hneH] using hrootDir 5 (by simp)
    · simpa using hroot6
    · simpa [hframe _ (hltH (t1 7 (by omega)) (by decide)) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hneH] using hrootDir 7 (by simp)
    · simpa [hframe _ (hltH (t1 8 (by omega)) (by decide)) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hneH] using hrootDir 8 (by simp)
    · simpa using hroot9
    · simpa using hroot10
    · simpa [hframe _ (hltH (t1 11 (by omega)) (by decide)) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hneH] using hrootDir 11 (by simp)
    · simpa using hroot12
    · simpa using hroot13
    · simpa [hframe _ (hltH (t1 14 (by omega)) (by decide)) (by omega) (by omega) (by omega)
        (by omega) (by omega) (by omega) (by omega) hneH] using hrootDir 14 (by simp)
    · simpa using hroot15
  · intro j hj
    have hj8 : j < 8 := by simpa [List.length] using hj
    have hneR (k : ℕ) (hk : k < 16) : tok.handle + j ≠ root + k := fun h => by
      have ht := t2 j (by omega); rw [h, t1 k hk] at ht; omega
    by_cases h2 : j = 2
    · subst h2; simpa using hh2
    · rw [hframe _ (hltH (t2 j (by omega)) (by decide))
        (hneR 4 (by omega)) (hneR 6 (by omega)) (hneR 9 (by omega)) (hneR 10 (by omega))
        (hneR 12 (by omega)) (hneR 13 (by omega)) (hneR 15 (by omega)) (by omega)]
      have h0 := hdetect j hj
      interval_cases j <;> first | exact False.elim (h2 rfl) | simpa using h0
  · obtain ⟨hcnt, hmemL, hdist, hbits, hrev⟩ := hoffReady
    refine ⟨le_trans hcnt hcapLt.le, ?_, ?_, ?_, ?_⟩
    · intro j hj
      rw [holLo j (lt_of_lt_of_le hj hcnt)]
      exact ⟨lt_trans (hmemL j hj).1 hcapLt, (hioLo _ (hmemL j hj).1).trans (hmemL j hj).2⟩
    · intro j₁ hj₁ j₂ hj₂ hne
      rw [holLo j₁ (lt_of_lt_of_le hj₁ hcnt), holLo j₂ (lt_of_lt_of_le hj₂ hcnt)]
      exact hdist j₁ hj₁ j₂ hj₂ hne
    · intro e he
      by_cases hlt : e < tok.intCap
      · rw [hioLo e hlt]; exact hbits e hlt
      · rw [hioHi e (by omega) he]; exact Or.inl rfl
    · intro e he h1
      by_cases hlt : e < tok.intCap
      · rw [hioLo e hlt] at h1
        obtain ⟨j, hj, hje⟩ := hrev e hlt h1
        exact ⟨j, hj, (holLo j (lt_of_lt_of_le hj hcnt)).trans hje⟩
      · rw [hioHi e (by omega) he] at h1; omega
  · constructor
    · intro e heE; dsimp only
      obtain ⟨heiCap, hthr0, hbr0⟩ := hedgeAcc.1 e heE
      have hetEq : mem' (heap + 2 * newCap + model.extToInt e) =
          mem (tok.edgeThresholds + model.extToInt e) := hetLo _ heiCap
      have hslEq : mem' (heap + newCap + model.extToInt e) =
          mem (tok.slots + model.extToInt e) := hslLo _ heiCap
      have hioEq : mem' (heap + 5 * newCap + model.extToInt e) =
          mem (tok.inOffReady + model.extToInt e) := hioLo _ heiCap
      refine ⟨lt_trans heiCap hcapLt,
        by rw [hetEq]; exact hthr0.congr (fun j hj => hagT ((t1718 e heE).1 j hj) (by decide) (by decide) (by decide)), ?_⟩
      by_cases hin : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E
      · simp only [hin, ↓reduceIte] at hbr0 ⊢
        obtain ⟨hsnz, his, hnm, hst, val, acc, hp, hfl, hac, hd⟩ := hbr0
        rw [hslEq]
        exact ⟨hsnz, his, (hagT (t10 _ his.2) (by decide) (by decide) (by decide)).trans hnm,
          (hagT (t11 _ his.2) (by decide) (by decide) (by decide)).trans (hst.trans hetEq.symm),
          val, acc, hp, hfl, hac, hd⟩
      · simp only [hin, ↓reduceIte] at hbr0 ⊢
        obtain ⟨hs0, val, acc, hrec0, hfl, hac, hd, hpush⟩ := hbr0
        have herEq : mem' (heap + 3 * newCap + model.extToInt e) =
            mem (tok.edgeRecords + model.extToInt e) := herLo _ heiCap
        refine ⟨hslEq.trans hs0, val, acc, ?_, hfl, hac, hd, fun hn => hioEq.trans (hpush hn)⟩
        rw [herEq]
        exact hrec0.congr (fun a ha1 ha2 => by
          have haIdx : a = mem (tok.edgeRecords + model.extToInt e) +
              (a - mem (tok.edgeRecords + model.extToInt e)) := by omega
          rw [haIdx]; exact hagT ((t1718 e heE).2 hin _ (by omega)) (by decide) (by decide) (by decide))
    · intro slot val his hp
      have hnmEq : mem' (tok.names + slot) = mem (tok.names + slot) :=
        hagT (t10 slot his.2) (by decide) (by decide) (by decide)
      obtain ⟨h1, h2, h3, h4, h5⟩ := hedgeAcc.2 slot val his hp
      dsimp only
      rw [hnmEq]
      exact ⟨lt_trans h1 hcapLt, h2, (hslLo _ h1).trans h3, h4, h5⟩
  · intro i hi
    obtain ⟨hh, hbr, hcr⟩ := hcores i hi
    refine ⟨(hagT (t4 i (by omega)) (by decide) (by decide) (by decide)).trans hh,
      by
        have h1 : tok.handle + 18 + (cfg.P.d + 1) + i = tok.handle + 18 + (cfg.P.d + 1 + i) := by omega
        rw [h1] at hbr ⊢; exact (hagT (t4 _ (by omega)) (by decide) (by decide) (by decide)).trans hbr,
      (hlocalCore (tok.coreHandle i) _ (tok.coreTok i) mem mem' (hcore_ag i hi)).1 hcr⟩
  · obtain ⟨htabW, hrgW, hsubCap, hnsW, hglW⟩ := hwire
    refine ⟨fun j hj => (hagT (t3 j hj) (by decide) (by decide) (by decide)).trans (htabW j hj),
      hrgW.of_agree (fun a h1 h2 => hagT (t20 a h1 h2) (by decide) (by decide) (by decide)),
      ⟨hsubCap.1, fun ei hei => ⟨lt_trans (hsubCap.2 ei hei).1 hcapLt, (hsubCap.2 ei hei).2⟩⟩,
      ⟨fun ei hei => by
          rw [hslLo ei (hsubCap.2 ei hei).1]
          have hfwd := hnsW.forward ei hei
          have hslotLt : mem (tok.slots + ei) < 2 * tok.tree.n := by unfold isEdgeSlot at hfwd; omega
          exact ⟨hfwd.1, hfwd.2.1, (hagT (t10 _ hslotLt) (by decide) (by decide) (by decide)).trans hfwd.2.2⟩,
        fun k hk hks => by
          have hkLt : k < 2 * tok.tree.n := hks.2
          rw [hagT (t10 k hkLt) (by decide) (by decide) (by decide)]
          obtain ⟨hmem, hslot⟩ := hnsW.inverse k hk hks
          exact ⟨hmem, (hslLo _ (hsubCap.2 _ hmem).1).trans hslot⟩,
        fun ei hei => by
          rw [hslLo ei (hsubCap.2 ei hei).1]; exact hnsW.endpoints ei hei⟩,
      fun e he => by
        dsimp only
        have hgl := hglW e he; dsimp only at hgl
        have heiCap := (hedgeAcc.1 e he).1
        split_ifs at hgl ⊢ with hin
        · rw [hslLo _ heiCap]; exact hgl
        · intro val hpa
          rw [herLo _ heiCap] at hpa
          exact hgl val (hpa.congr fun x hlo hhi => by
            have hx : x = mem (tok.edgeRecords + model.extToInt e) +
                (x - mem (tok.edgeRecords + model.extToInt e)) := by omega
            rw [hx]; exact (hagT ((t1718 e he).2 hin _ (by omega)) (by decide) (by decide) (by decide)).symm)⟩
  · refine ⟨fun a h => by
        dsimp only at h
        by_cases h1 : heap ≤ a ∧ a < heap + 6 * newCap
        · exact Or.inr h1
        · simp only [show ¬ (heap ≤ a ∧ a < heap + newCap) by omega,
            show ¬ (heap + newCap ≤ a ∧ a < heap + 2 * newCap) by omega,
            show ¬ (heap + 2 * newCap ≤ a ∧ a < heap + 3 * newCap) by omega,
            show ¬ (heap + 3 * newCap ≤ a ∧ a < heap + 4 * newCap) by omega,
            show ¬ (heap + 4 * newCap ≤ a ∧ a < heap + 5 * newCap) by omega,
            show ¬ (heap + 5 * newCap ≤ a ∧ a < heap + 6 * newCap) by omega, ↓reduceIte] at h
          exact Or.inl (hOwn a h),
      fun j hj => htagKeep (t1 j hj) (by decide), fun j hj => htagKeep (t2 j hj) (by decide),
      fun j hj => htagKeep (t3 j hj) (by decide), fun j hj => htagKeep (t4 j hj) (by decide),
      fun j hj => htagKeep (t5 j hj) (by decide), htagKeep t6 (by decide),
      fun j hj => htagKeep (t7 j hj) (by decide),
      fun j hj => by
        dsimp only at hj ⊢
        rw [ite_eq_left ⟨by omega, by omega⟩],
      fun j hj => by
        dsimp only at hj ⊢
        rw [ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩],
      fun j hj => htagKeep (t10 j hj) (by decide), fun j hj => htagKeep (t11 j hj) (by decide),
      fun j hj => by
        dsimp only at hj ⊢
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩],
      fun j hj => by
        dsimp only at hj ⊢
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_left ⟨by omega, by omega⟩],
      fun j hj => by
        dsimp only at hj ⊢
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩],
      fun j hj => by
        dsimp only at hj ⊢
        rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
          ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_left ⟨by omega, by omega⟩],
      fun a ha => htagKeep (t16 a ha) (by decide),
      fun e he => ⟨fun j hj => by
          rw [hetLo _ (hedgeAcc.1 e he).1]; exact htagKeep ((t1718 e he).1 j hj) (by decide),
        fun hnot j hj => by
          rw [herLo _ (hedgeAcc.1 e he).1]; exact htagKeep ((t1718 e he).2 hnot j hj) (by decide)⟩,
      fun a ha => htagKeep (t19 a ha) (by decide),
      fun a h1 h2 => htagKeep (t20 a h1 h2) (by decide),
      fun i hi a ha => htagKeep (t21 i hi a ha) (by omega)⟩
  · dsimp only [solverStateRep]
    rw [(htreeLocal tok.treeHeap tok.tree tok.treeTok mem mem' htree_ag).2.symm,
      Finset.sum_congr rfl fun i _ =>
        (hlocalCore (tok.coreHandle i.val) (chainLevelOrdAbs model.chain i.val) (tok.coreTok i.val)
          mem mem' (hcore_ag i.val i.isLt)).2.symm]

end MinCostFlow.MinRatio
