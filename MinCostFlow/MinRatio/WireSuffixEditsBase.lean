module

public import MinCostFlow.MinRatio.TreeEditLayout
public import MinCostFlow.DynSpanner.Program.StateLayout
import WordRAM.Tactic

/-!
# Multi-forest suffix tree-edit packer: definitions and marking passes (`WireSuffixEditsBase`)

Defines `markForestListStmt`, `emitForestListDiffStmt`, `wireSuffixPackEditsBody`, the edge-union
and forest-pointer-list predicates (`graphListEdgeUnion`, `graphListEdgeSum`, `ForestPtrListAt`),
and proves the Pass 1–2 marking specification (`markForestListStmt_runs`) together with the
deduplicating scan list `emitScanList` used in `WireSuffixEdits.lean`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Chain MinCostFlow.DynSpanner.Program

/-! ### Procedures -/

/-- Mark `markBase[e] := 1` for every edge `e` of every `DynGraphAt` in `ptrs[0..cnt-1]`.
Inputs: `reg 10 = ptrs`, `reg 2 = cnt`, `reg 11 = markBase`. Clobbers: `reg 12..19`. -/
@[expose] def markForestListStmt : Stmt :=
  .assign 12 (.const 0) ;;
  .loop (.bin .lt (.reg 12) (.reg 2))
    (.assign 13 (.load (.bin .add (.reg 10) (.reg 12))) ;;
     .assign 14 (.load (.reg 13)) ;;
     .assign 15 (.load (.bin .add (.reg 13) (.const 1))) ;;
     .assign 16 (.load (.bin .add (.reg 13) (.const 3))) ;;
     .assign 17 (.bin .add (.bin .add (.bin .add (.reg 13) (.const 4))
       (.bin .mul (.const 7) (.reg 14))) (.reg 15)) ;;
     .assign 18 (.const 0) ;;
     .loop (.bin .lt (.reg 18) (.reg 16))
       (.assign 19 (.load (.bin .add (.reg 17) (.reg 18))) ;;
        .store (.bin .add (.reg 11) (.reg 19)) (.const 1) ;;
        .assign 18 (.bin .add (.reg 18) (.const 1))) ;;
     .assign 12 (.bin .add (.reg 12) (.const 1)))

/-- Scan `ptrs[0..cnt-1]` and emit `[tag, e]` into `outBuf + 2 * outLen` whenever
`otherMark[e] = 0` and `emitMark[e] = 0`, setting `emitMark[e] := 1` and incrementing `outLen`.
Inputs: `reg 10 = ptrs`, `reg 2 = cnt`, `reg 11 = otherMark`, `reg 7 = emitMark`,
`reg 8 = outBuf`, `reg 9 = outLen`, `reg 20 = tag`. Clobbers: `reg 12..19`, updates `reg 9`. -/
@[expose] def emitForestListDiffStmt : Stmt :=
  .assign 12 (.const 0) ;;
  .loop (.bin .lt (.reg 12) (.reg 2))
    (.assign 13 (.load (.bin .add (.reg 10) (.reg 12))) ;;
     .assign 14 (.load (.reg 13)) ;;
     .assign 15 (.load (.bin .add (.reg 13) (.const 1))) ;;
     .assign 16 (.load (.bin .add (.reg 13) (.const 3))) ;;
     .assign 17 (.bin .add (.bin .add (.bin .add (.reg 13) (.const 4))
       (.bin .mul (.const 7) (.reg 14))) (.reg 15)) ;;
     .assign 18 (.const 0) ;;
     .loop (.bin .lt (.reg 18) (.reg 16))
       (.assign 19 (.load (.bin .add (.reg 17) (.reg 18))) ;;
        .cond (.bin .eq (.load (.bin .add (.reg 11) (.reg 19))) (.const 0))
          (.cond (.bin .eq (.load (.bin .add (.reg 7) (.reg 19))) (.const 0))
            (.store (.bin .add (.reg 7) (.reg 19)) (.const 1) ;;
             .store (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.reg 20) ;;
             .store (.bin .add (.bin .add (.reg 8) (.bin .mul (.const 2) (.reg 9))) (.const 1))
               (.reg 19) ;;
             .assign 9 (.bin .add (.reg 9) (.const 1)))
            .nop)
          .nop ;;
        .assign 18 (.bin .add (.reg 18) (.const 1))) ;;
     .assign 12 (.bin .add (.reg 12) (.const 1)))

/-- Complete multi-forest edit packer taking `[oldPtrs, newPtrs, cnt, intCap, heap]` (`reg 0..4`),
writing `TreeEditsAt` at `heap + 3 * intCap`, and returning the edit count `edits.length`. -/
@[expose] def wireSuffixPackEditsBody : Stmt :=
  .assign 5 (.reg 4) ;;
  .assign 6 (.bin .add (.reg 4) (.reg 3)) ;;
  .assign 7 (.bin .add (.reg 6) (.reg 3)) ;;
  .assign 8 (.bin .add (.reg 7) (.reg 3)) ;;
  .assign 9 (.const 0) ;;
  .assign 10 (.reg 0) ;;
  .assign 11 (.reg 5) ;;
  markForestListStmt ;;
  .assign 10 (.reg 1) ;;
  .assign 11 (.reg 6) ;;
  markForestListStmt ;;
  .assign 10 (.reg 0) ;;
  .assign 11 (.reg 6) ;;
  .assign 20 (.const 0) ;;
  emitForestListDiffStmt ;;
  .assign 10 (.reg 1) ;;
  .assign 11 (.reg 5) ;;
  .assign 20 (.const 1) ;;
  emitForestListDiffStmt ;;
  .ret (.reg 9)

theorem markForestListStmt_noRand : markForestListStmt.NoRand := by
  simp [markForestListStmt, Stmt.NoRand]

theorem emitForestListDiffStmt_noRand : emitForestListDiffStmt.NoRand := by
  simp [emitForestListDiffStmt, Stmt.NoRand]

theorem wireSuffixPackEditsBody_noRand : wireSuffixPackEditsBody.NoRand := by
  simp [wireSuffixPackEditsBody, markForestListStmt_noRand, emitForestListDiffStmt_noRand, Stmt.NoRand]

/-! ### Graph-list union, edge sum, and pointer layout -/

/-- The union of edge sets of a list of graphs `Fs`. -/
@[expose] def graphListEdgeUnion (Fs : List MGraph) : Finset ℕ :=
  Fs.foldl (fun acc F => acc ∪ F.E) ∅

/-- Total edge count across a list of graphs `Fs`. -/
@[expose] def graphListEdgeSum (Fs : List MGraph) : ℕ :=
  (Fs.map MGraph.m).sum

theorem mem_graphListEdgeUnion {Fs : List MGraph} {e : ℕ} :
    e ∈ graphListEdgeUnion Fs ↔ ∃ F ∈ Fs, e ∈ F.E := by
  suffices h : ∀ (acc : Finset ℕ) (L : List MGraph),
      e ∈ L.foldl (fun s F => s ∪ F.E) acc ↔ e ∈ acc ∨ ∃ F ∈ L, e ∈ F.E by
    simpa [graphListEdgeUnion] using h ∅ Fs
  intro acc L
  induction L generalizing acc with
  | nil => simp
  | cons F rest ih =>
    simp only [List.foldl_cons, ih, Finset.mem_union, List.mem_cons]
    constructor
    · rintro ((hacc | hF) | ⟨G, hG, he⟩)
      · exact Or.inl hacc
      · exact Or.inr ⟨F, Or.inl rfl, hF⟩
      · exact Or.inr ⟨G, Or.inr hG, he⟩
    · rintro (hacc | ⟨G, rfl | hG, he⟩)
      · exact Or.inl (Or.inl hacc)
      · exact Or.inl (Or.inr he)
      · exact Or.inr ⟨G, hG, he⟩

theorem graphListEdgeUnion_append (L₁ L₂ : List MGraph) :
    graphListEdgeUnion (L₁ ++ L₂) = graphListEdgeUnion L₁ ∪ graphListEdgeUnion L₂ := by
  ext e
  simp only [Finset.mem_union, mem_graphListEdgeUnion, List.mem_append]
  constructor
  · rintro ⟨F, h1 | h2, he⟩
    · exact Or.inl ⟨F, h1, he⟩
    · exact Or.inr ⟨F, h2, he⟩
  · rintro (⟨F, h1, he⟩ | ⟨F, h2, he⟩)
    · exact ⟨F, Or.inl h1, he⟩
    · exact ⟨F, Or.inr h2, he⟩

theorem graphListEdgeSum_append (L₁ L₂ : List MGraph) :
    graphListEdgeSum (L₁ ++ L₂) = graphListEdgeSum L₁ + graphListEdgeSum L₂ := by
  simp [graphListEdgeSum]

/-- `ForestPtrListAt mem ptrBase Fs intCap bound`: `ptrBase[0..Fs.length-1]` holds pointers to
`DynGraphAt` layouts of `Fs[t]` strictly below `bound`, with all edges `< intCap`. -/
@[expose] def ForestPtrListAt (mem : ℕ → ℕ) (ptrBase : ℕ) (Fs : List MGraph)
    (intCap bound : ℕ) : Prop :=
  ptrBase + Fs.length ≤ bound ∧
  ∀ (t : ℕ) (ht : t < Fs.length),
    ∃ vc ec, DynGraphAt mem (mem (ptrBase + t)) vc ec Fs[t] ∧
      mem (ptrBase + t) + dynGraphSize vc ec ≤ bound ∧
      ∀ e ∈ Fs[t].E, e < intCap

theorem ForestPtrListAt.congr {mem mem' : ℕ → ℕ} {ptrBase intCap bound : ℕ} {Fs : List MGraph}
    (h : ForestPtrListAt mem ptrBase Fs intCap bound)
    (heq : ∀ a < bound, mem' a = mem a) :
    ForestPtrListAt mem' ptrBase Fs intCap bound := by
  have hlen : ptrBase + Fs.length ≤ bound := h.1
  refine ⟨hlen, fun t ht => ?_⟩
  obtain ⟨vc, ec, hG, hEnd, hCap⟩ := h.2 t ht
  have hptr : mem' (ptrBase + t) = mem (ptrBase + t) := heq _ (by omega)
  refine ⟨vc, ec, ?_, hptr.symm ▸ hEnd, hCap⟩
  rw [hptr]
  exact dynGraphAt_of_agree hG (fun a h1 h2 => heq a (by omega))

/-! ### Pass 1 & 2 marking proofs -/

private lemma markEdgeList_runs {w markBase intCap eList : ℕ} {p : Program} {ω : ℕ → Bool}
    {eL : List ℕ} {st : State}
    (h11 : st.regs 11 = markBase) (h16 : st.regs 16 = eL.length)
    (h17 : st.regs 17 = eList) (h18 : st.regs 18 = 0)
    (heL : ListAt st.mem eList eL) (heLlt : eList + eL.length ≤ markBase)
    (hCap : ∀ e ∈ eL, e < intCap)
    (hMarkW : markBase + intCap < 2 ^ w) (hLenW : eL.length < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out c,
      Runs w p ω
        (.loop (.bin .lt (.reg 18) (.reg 16))
          (.assign 19 (.load (.bin .add (.reg 17) (.reg 18))) ;;
           .store (.bin .add (.reg 11) (.reg 19)) (.const 1) ;;
           .assign 18 (.bin .add (.reg 18) (.const 1))))
        st .normal out c ∧
      c ≤ 25 * eL.length + 5 ∧
      (∀ e < intCap, out.mem (markBase + e) = if e ∈ eL then 1 else st.mem (markBase + e)) ∧
      (∀ a, a < markBase ∨ markBase + intCap ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r ≠ 18 → r ≠ 19 → out.regs r = st.regs r) := by
  suffices hLoop : ∀ (rest done : List ℕ) (s : State),
      done ++ rest = eL →
      s.regs 11 = markBase → s.regs 16 = eL.length → s.regs 17 = eList →
      s.regs 18 = done.length →
      (∀ a, a < markBase ∨ markBase + intCap ≤ a → s.mem a = st.mem a) →
      (∀ e < intCap, s.mem (markBase + e) = if e ∈ done then 1 else st.mem (markBase + e)) →
      ∃ out c,
        Runs w p ω
          (.loop (.bin .lt (.reg 18) (.reg 16))
            (.assign 19 (.load (.bin .add (.reg 17) (.reg 18))) ;;
             .store (.bin .add (.reg 11) (.reg 19)) (.const 1) ;;
             .assign 18 (.bin .add (.reg 18) (.const 1))))
          s .normal out c ∧
        c ≤ 25 * rest.length + 5 ∧
        (∀ e < intCap, out.mem (markBase + e) = if e ∈ eL then 1 else st.mem (markBase + e)) ∧
        (∀ a, a < markBase ∨ markBase + intCap ≤ a → out.mem a = st.mem a) ∧
        (∀ r, r ≠ 18 → r ≠ 19 → out.regs r = s.regs r) by
    exact hLoop eL [] st rfl h11 h16 h17 h18 (fun _ _ => rfl) (fun _ _ => by simp)
  intro rest
  induction rest with
  | nil =>
    intro done s happ _ h16' _ h18' hfr hmk
    have hdEq : done = eL := by simpa using happ
    subst hdEq
    refine ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, h18', h16'], rfl, rfl, by simp [Expr.size]⟩),
      by omega, hmk, hfr, fun _ _ _ => rfl⟩
  | cons e rest ih =>
    intro done s happ h11' h16' h17' h18' hfr hmk
    have hLen : done.length + rest.length + 1 = eL.length := by
      have := congrArg List.length happ; simp at this; omega
    have heMem : e ∈ eL := by rw [← happ]; simp
    have heCap : e < intCap := hCap e heMem
    have heAt : s.mem (eList + done.length) = e := by
      rw [hfr _ (Or.inl (by omega))]
      have hget := heL done.length (by omega)
      have heq : eL[done.length]'(by omega) = e := by
        have h1 : (done ++ e :: rest)[done.length]'(by simp) = e := by simp
        simpa [happ] using h1
      exact hget.trans heq
    let s1 := { s with regs := Function.update s.regs 19 e }
    let s2 := { s1 with mem := Function.update s1.mem (markBase + e) 1 }
    let s3 := { s2 with regs := Function.update s2.regs 18 (done.length + 1) }
    have r1 : Runs w p ω (.assign 19 (.load (.bin .add (.reg 17) (.reg 18)))) s .normal s1 5 :=
      runs_assign_iff.mpr ⟨e, by simp [Expr.eval, BinOp.eval, h17', h18',
        show eList + done.length < 2 ^ w by omega, heAt], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.store (.bin .add (.reg 11) (.reg 19)) (.const 1)) s1 .normal s2 5 :=
      runs_store_iff.mpr ⟨markBase + e, 1, by simp [Expr.eval, BinOp.eval, s1, Function.update_of_ne,
        h11', show markBase + e < 2 ^ w by omega], by simp [Expr.eval, hw1], rfl, rfl, rfl⟩
    have r3 : Runs w p ω (.assign 18 (.bin .add (.reg 18) (.const 1))) s2 .normal s3 4 :=
      runs_assign_iff.mpr ⟨done.length + 1, by simp [Expr.eval, BinOp.eval, s2, s1,
        Function.update_of_ne, h18', hw1, show done.length + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    have rBody : Runs w p ω _ s .normal s3 (5 + (5 + 4 + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1, runs_seq_iff.mpr (Or.inr ⟨s2, 5, 4, r2, r3, rfl⟩), rfl⟩)
    obtain ⟨out, cRest, rRest, hcRest, hmkEnd, hfrEnd, hregsEnd⟩ :=
      ih (done ++ [e]) s3 (by simpa [List.append_assoc] using happ)
        (by simp [s3, s2, s1, Function.update_of_ne, h11'])
        (by simp [s3, s2, s1, Function.update_of_ne, h16'])
        (by simp [s3, s2, s1, Function.update_of_ne, h17'])
        (by simp [s3])
        (fun a ha => by
          change Function.update s.mem (markBase + e) 1 a = st.mem a
          rw [Function.update_of_ne (by omega)]; exact hfr a ha)
        (fun f hf => by
          change Function.update s.mem (markBase + e) 1 (markBase + f) = _
          by_cases hfe : f = e
          · subst hfe; simp
          · rw [Function.update_of_ne (by omega), hmk f hf]
            simp [hfe])
    refine ⟨out, (5 + (5 + 4 + 1) + 1) + cRest + 4,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s3, _, cRest,
        by simp [Expr.eval, BinOp.eval, h18', h16', show done.length < eL.length by omega,
          show w ≠ 0 by intro h; subst h; omega],
        by decide, rBody, rRest, by simp [Expr.size]; omega⟩)),
      by simp only [List.length_cons]; omega, hmkEnd, hfrEnd, fun r hr18 hr19 => by
        rw [hregsEnd r hr18 hr19]; simp [s3, s2, s1, Function.update_of_ne hr18, Function.update_of_ne hr19]⟩

/-- Execution theorem for `markForestListStmt`: marks `markBase[e] := 1` for every `e` in the
edge union of `Fs` in `O(Fs.length + graphListEdgeSum Fs)` steps. -/
theorem markForestListStmt_runs {w ptrs markBase intCap : ℕ} {Fs : List MGraph}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h10 : st.regs 10 = ptrs) (h2 : st.regs 2 = Fs.length) (h11 : st.regs 11 = markBase)
    (hFs : ForestPtrListAt st.mem ptrs Fs intCap markBase)
    (hMarkW : markBase + intCap < 2 ^ w) (hw7 : 7 < 2 ^ w) :
    ∃ out c,
      Runs w p ω markForestListStmt st .normal out c ∧
      c ≤ 25 * graphListEdgeSum Fs + 52 * Fs.length + 10 ∧
      (∀ e < intCap, out.mem (markBase + e) =
        if e ∈ graphListEdgeUnion Fs then 1 else st.mem (markBase + e)) ∧
      (∀ a, a < markBase ∨ markBase + intCap ≤ a → out.mem a = st.mem a) ∧
      (∀ r, r < 12 ∨ 20 ≤ r → out.regs r = st.regs r) := by
  let s0 := { st with regs := Function.update st.regs 12 0 }
  have r0 : Runs w p ω (.assign 12 (.const 0)) st .normal s0 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
  suffices hLoop : ∀ (rest done : List MGraph) (s : State),
      done ++ rest = Fs →
      s.regs 10 = ptrs → s.regs 2 = Fs.length → s.regs 11 = markBase →
      s.regs 12 = done.length →
      (∀ a, a < markBase ∨ markBase + intCap ≤ a → s.mem a = st.mem a) →
      (∀ e < intCap, s.mem (markBase + e) =
        if e ∈ graphListEdgeUnion done then 1 else st.mem (markBase + e)) →
      ∃ out c,
        Runs w p ω
          (.loop (.bin .lt (.reg 12) (.reg 2))
            (.assign 13 (.load (.bin .add (.reg 10) (.reg 12))) ;;
             .assign 14 (.load (.reg 13)) ;;
             .assign 15 (.load (.bin .add (.reg 13) (.const 1))) ;;
             .assign 16 (.load (.bin .add (.reg 13) (.const 3))) ;;
             .assign 17 (.bin .add (.bin .add (.bin .add (.reg 13) (.const 4))
               (.bin .mul (.const 7) (.reg 14))) (.reg 15)) ;;
             .assign 18 (.const 0) ;;
             .loop (.bin .lt (.reg 18) (.reg 16))
               (.assign 19 (.load (.bin .add (.reg 17) (.reg 18))) ;;
                .store (.bin .add (.reg 11) (.reg 19)) (.const 1) ;;
                .assign 18 (.bin .add (.reg 18) (.const 1))) ;;
             .assign 12 (.bin .add (.reg 12) (.const 1))))
          s .normal out c ∧
        c ≤ 25 * graphListEdgeSum rest + 52 * rest.length + 5 ∧
        (∀ e < intCap, out.mem (markBase + e) =
          if e ∈ graphListEdgeUnion Fs then 1 else st.mem (markBase + e)) ∧
        (∀ a, a < markBase ∨ markBase + intCap ≤ a → out.mem a = st.mem a) ∧
        (∀ r, r < 12 ∨ 20 ≤ r → out.regs r = s.regs r) by
    obtain ⟨out, cL, rL, hcL, hmk, hfr, hregs⟩ :=
      hLoop Fs [] s0 rfl (by simp [s0, Function.update_of_ne, h10])
        (by simp [s0, Function.update_of_ne, h2]) (by simp [s0, Function.update_of_ne, h11])
        (by simp [s0]) (fun _ _ => rfl) (fun _ _ => by simp [s0, graphListEdgeUnion])
    refine ⟨out, 2 + cL + 1, runs_seq_iff.mpr (Or.inr ⟨s0, 2, cL, r0, rL, rfl⟩),
      by omega, hmk, hfr, fun r hr => by
        rw [hregs r hr]; exact Function.update_of_ne (by omega) _ _⟩
  intro rest
  induction rest with
  | nil =>
    intro done s happ _ h2' _ h12' hfr hmk
    have hdEq : done = Fs := by simpa using happ
    subst hdEq
    refine ⟨s, 4, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, h12', h2'], rfl, rfl, by simp [Expr.size]⟩),
      by simp [graphListEdgeSum], hmk, hfr, fun _ _ => rfl⟩
  | cons F rest ih =>
    intro done s happ h10' h2' h11' h12' hfr hmk
    have hLen : done.length + rest.length + 1 = Fs.length := by
      have := congrArg List.length happ; simp at this; omega
    have hFsEq : Fs[done.length]'(by omega) = F := by
      have h1 : (done ++ F :: rest)[done.length]'(by simp) = F := by simp
      simpa [happ] using h1
    obtain ⟨vc, ec, hG0, hGEnd, hFCap⟩ := hFs.2 done.length (by omega)
    rw [hFsEq] at hG0 hFCap
    let ptr := st.mem (ptrs + done.length)
    have hptrEq : s.mem (ptrs + done.length) = ptr := hfr _ (Or.inl (by have := hFs.1; omega))
    have hG : DynGraphAt s.mem ptr vc ec F :=
      dynGraphAt_of_agree hG0 (fun a h1 h2 => hfr a (Or.inl (by omega)))
    obtain ⟨eL, heLLen, _, heLMem, heLAt, _⟩ := hG.2.2.2.2.2.2.2.2.2.2.2.2.1
    have hvc : s.mem ptr = vc := hG.2.2.2.1
    have hec : s.mem (ptr + 1) = ec := hG.2.2.2.2.1
    have hmF : s.mem (ptr + 3) = F.m := hG.2.2.2.2.2.2.1
    have hdgSz : dynGraphSize vc ec = 4 + 7 * vc + 9 * ec := rfl
    have hptrW : ptrs + done.length < 2 ^ w := by have := hFs.1; omega
    let eList := dgEListBase ptr vc ec
    let s1 := { s with regs := Function.update s.regs 13 ptr }
    let s2 := { s1 with regs := Function.update s1.regs 14 vc }
    let s3 := { s2 with regs := Function.update s2.regs 15 ec }
    let s4 := { s3 with regs := Function.update s3.regs 16 F.m }
    let s5 := { s4 with regs := Function.update s4.regs 17 eList }
    let s6 := { s5 with regs := Function.update s5.regs 18 0 }
    have r1 : Runs w p ω (.assign 13 (.load (.bin .add (.reg 10) (.reg 12)))) s .normal s1 5 :=
      runs_assign_iff.mpr ⟨ptr, by simp [Expr.eval, BinOp.eval, h10', h12', hptrW, hptrEq], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.assign 14 (.load (.reg 13))) s1 .normal s2 3 :=
      runs_assign_iff.mpr ⟨vc, by simp [Expr.eval, s1, hvc], rfl, rfl, rfl⟩
    have r3 : Runs w p ω (.assign 15 (.load (.bin .add (.reg 13) (.const 1)))) s2 .normal s3 5 :=
      runs_assign_iff.mpr ⟨ec, by simp [Expr.eval, BinOp.eval, s2, s1, Function.update_of_ne,
        show 1 < 2 ^ w by omega, show ptr + 1 < 2 ^ w by omega, hec], rfl, rfl, rfl⟩
    have r4 : Runs w p ω (.assign 16 (.load (.bin .add (.reg 13) (.const 3)))) s3 .normal s4 5 :=
      runs_assign_iff.mpr ⟨F.m, by simp [Expr.eval, BinOp.eval, s3, s2, s1, Function.update_of_ne,
        show 3 < 2 ^ w by omega, show ptr + 3 < 2 ^ w by omega, hmF], rfl, rfl, rfl⟩
    have r5 : Runs w p ω
        (.assign 17 (.bin .add (.bin .add (.bin .add (.reg 13) (.const 4))
          (.bin .mul (.const 7) (.reg 14))) (.reg 15))) s4 .normal s5 10 :=
      runs_assign_iff.mpr ⟨eList, by simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, Function.update_of_ne,
        show 4 < 2 ^ w by omega, hw7, show ptr + 4 < 2 ^ w by omega, show 7 * vc < 2 ^ w by omega,
        show ptr + 4 + 7 * vc < 2 ^ w by omega, show ptr + 4 + 7 * vc + ec < 2 ^ w by omega,
        eList, dgEListBase], rfl, rfl, rfl⟩
    have r6 : Runs w p ω (.assign 18 (.const 0)) s5 .normal s6 2 :=
      runs_assign_iff.mpr ⟨0, by simp [Expr.eval, Nat.two_pow_pos w], rfl, rfl, rfl⟩
    have hmLeEc : F.m ≤ ec := by
      have hsub : F.E ⊆ Finset.range ec := fun x hx => Finset.mem_range.mpr (hG.2.2.1 x hx)
      simpa [MGraph.m] using Finset.card_le_card hsub
    obtain ⟨s7, cIn, rIn, hcIn, hmk7, hfr7, hregs7⟩ :=
      markEdgeList_runs (w := w) (markBase := markBase) (intCap := intCap) (eList := eList)
        (eL := eL) (st := s6) (by simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne, h11'])
        (by simp [s6, s5, s4, Function.update_of_ne, heLLen])
        (by simp [s6, s5, Function.update_of_ne]) (by simp [s6]) heLAt
        (by unfold eList dgEListBase; omega) (fun e he => hFCap e ((heLMem e).mp he))
        hMarkW (by omega) (by omega)
    let s8 := { s7 with regs := Function.update s7.regs 12 (done.length + 1) }
    have hs7_12 : s7.regs 12 = done.length := by
      rw [hregs7 12 (by decide) (by decide)]
      simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne, h12']
    have r8 : Runs w p ω (.assign 12 (.bin .add (.reg 12) (.const 1))) s7 .normal s8 4 :=
      runs_assign_iff.mpr ⟨done.length + 1, by simp [Expr.eval, BinOp.eval, hs7_12,
        show 1 < 2 ^ w by omega, show done.length + 1 < 2 ^ w by have := hFs.1; omega], rfl, rfl, rfl⟩
    have rBody : Runs w p ω _ s .normal s8 (5 + (3 + (5 + (5 + (10 + (2 + (cIn + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 3, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 5, _, r3,
      runs_seq_iff.mpr (Or.inr ⟨s4, 5, _, r4,
      runs_seq_iff.mpr (Or.inr ⟨s5, 10, _, r5,
      runs_seq_iff.mpr (Or.inr ⟨s6, 2, _, r6,
      runs_seq_iff.mpr (Or.inr ⟨s7, cIn, 4, rIn, r8, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)
    obtain ⟨out, cRest, rRest, hcRest, hmkEnd, hfrEnd, hregsEnd⟩ :=
      ih (done ++ [F]) s8 (by simpa [List.append_assoc] using happ)
        (by simp [s8, hregs7 10 (by decide) (by decide), s6, s5, s4, s3, s2, s1, Function.update_of_ne, h10'])
        (by simp [s8, hregs7 2 (by decide) (by decide), s6, s5, s4, s3, s2, s1, Function.update_of_ne, h2'])
        (by simp [s8, hregs7 11 (by decide) (by decide), s6, s5, s4, s3, s2, s1, Function.update_of_ne, h11'])
        (by simp [s8])
        (fun a ha => (hfr7 a ha).trans (hfr a ha))
        (fun e he => by
          change s7.mem (markBase + e) = _
          rw [hmk7 e he, show s6.mem (markBase + e) = s.mem (markBase + e) from rfl, hmk e he,
            graphListEdgeUnion_append]
          have hSing : graphListEdgeUnion [F] = F.E := by simp [graphListEdgeUnion]
          rw [hSing]
          by_cases hfe : e ∈ F.E
          · simp [(heLMem e).mpr hfe, hfe]
          · simp [show e ∉ eL from fun h => hfe ((heLMem e).mp h), hfe])
    refine ⟨out, (5 + (3 + (5 + (5 + (10 + (2 + (cIn + 4 + 1) + 1) + 1) + 1) + 1) + 1) + 1) + cRest + 4,
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s8, _, cRest,
        by simp [Expr.eval, BinOp.eval, h12', h2', show done.length < Fs.length by omega,
          show w ≠ 0 by intro h; subst h; omega],
        by decide, rBody, rRest, by simp [Expr.size]; omega⟩)),
      ?_, hmkEnd, hfrEnd, fun r hr => by
        rw [hregsEnd r hr]
        change Function.update s7.regs 12 _ r = _
        rw [Function.update_of_ne (by omega), hregs7 r (by omega) (by omega)]
        simp [s6, s5, s4, s3, s2, s1, Function.update_of_ne (by omega : r ≠ 18),
          Function.update_of_ne (by omega : r ≠ 17), Function.update_of_ne (by omega : r ≠ 16),
          Function.update_of_ne (by omega : r ≠ 15), Function.update_of_ne (by omega : r ≠ 14),
          Function.update_of_ne (by omega : r ≠ 13)]⟩
    simp only [graphListEdgeSum, List.map_cons, List.sum_cons, List.length_cons] at hcRest ⊢
    rw [heLLen] at hcIn
    omega

/-! ### Deduplicating emit scan list -/

/-- The deduplicated list of newly emitted elements when scanning `L` against `otherSet` and
an already-emitted set `emitted`. -/
@[expose] def emitScanList (otherSet : Finset ℕ) (emitted : Finset ℕ) : List ℕ → List ℕ
  | [] => []
  | e :: rest =>
    if e ∉ otherSet ∧ e ∉ emitted then e :: emitScanList otherSet (insert e emitted) rest
    else emitScanList otherSet emitted rest

theorem emitScanList_props (otherSet emitted : Finset ℕ) (L : List ℕ) :
    (emitScanList otherSet emitted L).Nodup ∧
    (∀ e, e ∈ emitScanList otherSet emitted L ↔ e ∈ L ∧ e ∉ otherSet ∧ e ∉ emitted) ∧
    (emitScanList otherSet emitted L).length ≤ L.length := by
  induction L generalizing emitted with
  | nil => simp [emitScanList]
  | cons a rest ih =>
    unfold emitScanList
    split_ifs with h
    · obtain ⟨hnd, hmem, hlen⟩ := ih (insert a emitted)
      refine ⟨List.nodup_cons.mpr ⟨fun ha => ((hmem a).mp ha).2.2 (Finset.mem_insert_self _ _), hnd⟩,
        fun e => ?_, by simp; omega⟩
      simp only [List.mem_cons, hmem, Finset.mem_insert, not_or]
      constructor
      · rintro (rfl | ⟨hr, ho, _, he⟩)
        · exact ⟨Or.inl rfl, h.1, h.2⟩
        · exact ⟨Or.inr hr, ho, he⟩
      · rintro ⟨rfl | hr, ho, he⟩
        · exact Or.inl rfl
        · by_cases hea : e = a
          · exact Or.inl hea
          · exact Or.inr ⟨hr, ho, hea, he⟩
    · obtain ⟨hnd, hmem, hlen⟩ := ih emitted
      refine ⟨hnd, fun e => ?_, by simp; omega⟩
      simp only [hmem, List.mem_cons]
      constructor
      · rintro ⟨hr, ho, he⟩; exact ⟨Or.inr hr, ho, he⟩
      · rintro ⟨rfl | hr, ho, he⟩
        · exact (h ⟨ho, he⟩).elim
        · exact ⟨hr, ho, he⟩

theorem emitScanList_append (otherSet emitted : Finset ℕ) (L₁ L₂ : List ℕ) :
    emitScanList otherSet emitted (L₁ ++ L₂) =
      emitScanList otherSet emitted L₁ ++
      emitScanList otherSet (emitted ∪ (emitScanList otherSet emitted L₁).toFinset) L₂ := by
  induction L₁ generalizing emitted with
  | nil => simp [emitScanList]
  | cons a rest ih =>
    simp only [List.cons_append, emitScanList]
    split_ifs with h
    · rw [List.cons_append, ih (insert a emitted)]
      congr 2
      ext x; simp
    · exact ih emitted

end MinCostFlow.MinRatio
