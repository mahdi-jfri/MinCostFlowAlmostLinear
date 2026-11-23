module

public import MinCostFlow.SparseCore.Program.AssemblyFirstOutEdges
public import MinCostFlow.SparseCore.Program.AssemblyFirstRot
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourMarks
public import MinCostFlow.SparseCore.Program.AssemblyBranchTour
public import MinCostFlow.SparseCore.Program.AssemblyBranchInitIface
public import MinCostFlow.SparseCore.Program.BundleTourInterface
public import MinCostFlow.SparseCore.Program.CompSplitListModel

import WordRAM.Tactic

/-!
# Rotation list `T₀` builder and interfaces of P2 and P4 (`AssemblyFirstRotProg`)

Provides two pieces for the first phases of a branch (`AsmBrCoreStepAt` and `AsmBrCoreInitAt`):

1. **Deterministic `T₀` builder (`asmFirstBuildRotStmt`, `asmFirstBuildRot_runs`,
   `asmFirstBuildRot_cover_runs`)**:
   - Given a raw candidate vertex array `rawPtr[0..m)` (`rawL : List ℕ`, `∀ v ∈ rawL, v < vCap`),
     copies it to `[h + 1 + m, h + 1 + 2 * m)`, sorts via `mergeSort` using scratch
     `[h + 1 + 2 * m, h + 1 + 3 * m)`, deduplicates into `[h + 1, h + 1 + |T₀|)`, stores `|T₀|`
     at `h`, and returns `h + 1 + 3 * m`.
   - Uses `1 + 3 * m` space (free of `vCap`), cost `≤ 280 * m * (log₂ (m + 1) + 1) + 150`, and
     delivers all `T₀` postconditions of `AsmBrCoreStepAt` (`T₀.Nodup`, `∀ v ∈ T₀, v < vCap`,
     `OutRotCover`, `st'.mem h = T₀.length`, `ListAt st'.mem (h + 1) T₀`, `OutCellsFree`, and
     `T₀.length ≤ 8 * (Enc(U_S) + words + editWords + 1)` when `rawL.toFinset = asmFirstRotSet`).
2. **Interfaces of P4 and P2**:
   - `AsmFirstCompSplitListAt`: P4's ordered split list of `canonCoreBatch`.
   - `AsmFirstTourInitAt`: P2's tour initialization from `OrdListAt` and `ExportAt` of `F`.
   - `AsmFirstTourRootAt`: P2's `rootOf` query (operation `10` of `tourContract`).
   - `AsmFirstTourBundleProj`: P2's projection to P5's `BundleTourAt`.
   (Together with `AsmFirstTourBlockStepAt` in `AssemblyFirstTourMarks.lean`.)
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

/-! ## 1. Deterministic `T₀` sort-and-dedup builder -/

@[expose] public section

/-- **Builder for `T₀`**, `[rawPtr, m, h]`, calling `sortProcs bSort`.
Copies `rawPtr[0..m)` to `[h + 1 + m, h + 1 + 2 * m)`, sorts in place using scratch
`[h + 1 + 2 * m, h + 1 + 3 * m)`, deduplicates into `[h + 1, h + 1 + |T₀|)`, writes `|T₀|` at
`h`, and returns `h + 1 + 3 * m`. -/
def asmFirstBuildRotStmt (bSort : ℕ) : Stmt :=
  .assign 3 (.bin .add (.reg 2) (.const 1)) ;;                              -- outPtr := h + 1
  .assign 4 (.bin .add (.reg 3) (.reg 1)) ;;                                -- arrPtr := h + 1 + m
  .assign 5 (.bin .add (.reg 4) (.reg 1)) ;;                                -- scrPtr := h + 1 + 2*m
  .assign 6 (.bin .add (.reg 5) (.reg 1)) ;;                                -- hEnd   := h + 1 + 3*m
  forRange 7 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 4) (.reg 7)) (.load (.bin .add (.reg 0) (.reg 7)))) ;;
  .call 8 (bSort + sortIdxMergeSort) [.reg 4, .reg 1, .reg 5] ;;
  .call 9 (bSort + sortIdxDedup) [.reg 4, .reg 1, .reg 3] ;;
  .store (.reg 2) (.reg 9) ;;
  .ret (.reg 6)

end

public section

theorem asmFirstBuildRotStmt_noRand (bSort : ℕ) : (asmFirstBuildRotStmt bSort).NoRand := by
  simp [asmFirstBuildRotStmt, forRange, forUp, Stmt.NoRand]

end

private lemma sortedDedup_length_le' : ∀ (L : List ℕ), (sortedDedup L).length ≤ L.length := by
  have haux : ∀ (prev : ℕ) (xs : List ℕ), (sortedDedupAux prev xs).length ≤ xs.length := by
    intro prev xs
    induction xs generalizing prev with
    | nil => simp [sortedDedupAux]
    | cons x xs ih =>
      unfold sortedDedupAux
      split_ifs
      · exact le_trans (ih prev) (Nat.le_succ _)
      · simp only [List.length_cons]; exact Nat.succ_le_succ (ih x)
  intro L
  cases L with
  | nil => simp [sortedDedup]
  | cons x xs => simp only [sortedDedup, List.length_cons]; exact Nat.succ_le_succ (haux x xs)

public section

/-- **Verification of `asmFirstBuildRotStmt`**: sorts and deduplicates `rawL` (`ListAt mem₀ rawPtr rawL`)
into `T₀ = rawL.toFinset.sort (· ≤ ·)`, writing `[|T₀|, T₀...]` at `h`, returning `h + 1 + 3 * rawL.length`,
leaving memory below `h` unchanged, and running in `≤ 280 * rawL.length * (Nat.log 2 (rawL.length + 1) + 1) + 150`
time. -/
theorem asmFirstBuildRot_runs {w bSort rawPtr vCap h pos : ℕ} {p : Program}
    (hp : p.HasAt bSort (sortProcs bSort))
    {rawL : List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hw16 : 16 ≤ 2 ^ w)
    (hraw : ListAt mem₀ rawPtr rawL) (hraw_le : rawPtr + rawL.length ≤ h)
    (hraw_cap : ∀ v ∈ rawL, v < vCap) (hvCap_w : vCap < 2 ^ w)
    (hz : ZeroFrom mem₀ h)
    (hsp : h + 1 + 3 * rawL.length < 2 ^ w) :
    let T₀ := rawL.toFinset.sort (· ≤ ·)
    ∃ o st' c,
      Runs w p ω (asmFirstBuildRotStmt bSort) (startState [rawPtr, rawL.length, h] mem₀ pos) o st' c ∧
      o.value = h + 1 + 3 * rawL.length ∧
      st'.mem h = T₀.length ∧
      ListAt st'.mem (h + 1) T₀ ∧
      T₀.Nodup ∧
      (∀ v ∈ T₀, v < vCap) ∧
      T₀.length ≤ rawL.length ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem₀ a) ∧
      c ≤ 280 * rawL.length * (Nat.log 2 (rawL.length + 1) + 1) + 150 := by
  intro T₀
  set m := rawL.length
  set outPtr := h + 1
  set arrPtr := outPtr + m
  set scrPtr := arrPtr + m
  set hEnd := scrPtr + m
  have hraw_w : ∀ x ∈ rawL, x < 2 ^ w := fun x hx => lt_trans (hraw_cap x hx) hvCap_w
  -- Loop invariant: copied `rawL[0..i)` into `[arrPtr, arrPtr + i)`.
  let invC : ℕ → State → Prop := fun i st =>
    st.regs 0 = rawPtr ∧ st.regs 1 = m ∧ st.regs 2 = h ∧
    st.regs 3 = outPtr ∧ st.regs 4 = arrPtr ∧ st.regs 5 = scrPtr ∧ st.regs 6 = hEnd ∧
    st.regs 7 = i ∧
    (∀ j (hj : j < i), ∀ hjm : j < rawL.length, st.mem (arrPtr + j) = rawL[j]'hjm) ∧
    (∀ a, a < arrPtr ∨ arrPtr + i ≤ a → st.mem a = mem₀ a)
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 7) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 4) (.reg 7)) (.load (.bin .add (.reg 0) (.reg 7))))
    (P := fun st => invC 0 { st with regs := Function.update st.regs 7 0 })
    (Inv := invC) (fun _ => 12) 0 m (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st hI => ⟨Expr.eval_const (by omega), hI⟩)
    (fun _ _ _ _ hI => hI.2.2.2.2.2.2.2.1)
    (fun _ _ _ _ hI => Expr.eval_reg_of_eq hI.2.1)
    (fun i _ hi st ω' hI => by
      obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, hcp, hfr⟩ := hI
      have hsrc : st.mem (rawPtr + i) = rawL[i]'hi := by
        rw [hfr (rawPtr + i) (Or.inl (by omega))]; exact hraw i hi
      refine ⟨.normal, { st with mem := Function.update st.mem (arrPtr + i) (rawL[i]'hi) },
        (Expr.bin .add (.reg 4) (.reg 7)).size + (Expr.load (.bin .add (.reg 0) (.reg 7))).size + 1,
        runs_store_iff.mpr ⟨arrPtr + i, rawL[i]'hi,
          Expr.eval_add (Expr.eval_reg_of_eq r4) (Expr.eval_reg_of_eq r7) (by omega),
          Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq r0) (Expr.eval_reg_of_eq r7)
            (by omega)) hsrc, rfl, rfl, rfl⟩,
        ⟨⟨by simp [r0], by simp [r1], by simp [r2], by simp [r3], by simp [r4], by simp [r5],
          by simp [r6], by simp,
          fun j hj hjm => by
            by_cases hji : j = i
            · subst hji; simp [Function.update_self]
            · dsimp only; rw [Function.update_of_ne (by omega)]; exact hcp j (by omega) hjm,
          fun a ha => by
            dsimp only; rw [Function.update_of_ne (by omega)]; exact hfr a (by omega)⟩,
          r7⟩,
        by simp [Expr.size]⟩)
  -- Setup 4 assigns
  set s0 := startState [rawPtr, m, h] mem₀ pos
  set regs1 := Function.update s0.regs 3 outPtr
  set regs2 := Function.update regs1 4 arrPtr
  set regs3 := Function.update regs2 5 scrPtr
  set regs4 := Function.update regs3 6 hEnd
  have hr1 : Runs w p ω (.assign 3 (.bin .add (.reg 2) (.const 1))) s0 .normal ⟨mem₀, regs1, pos⟩
      ((Expr.bin .add (.reg 2) (.const 1)).size + 1) :=
    runs_assign_iff.mpr ⟨outPtr, Expr.eval_add (Expr.eval_reg_of_eq (v := h) (by simp [s0, startState]))
      (Expr.eval_const (by omega)) (by omega), rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 4 (.bin .add (.reg 3) (.reg 1))) ⟨mem₀, regs1, pos⟩ .normal
      ⟨mem₀, regs2, pos⟩ ((Expr.bin .add (.reg 3) (.reg 1)).size + 1) :=
    runs_assign_iff.mpr ⟨arrPtr, Expr.eval_add (Expr.eval_reg_of_eq (v := outPtr) (by simp [regs1]))
      (Expr.eval_reg_of_eq (v := m) (by simp [regs1, s0, startState])) (by omega), rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 5 (.bin .add (.reg 4) (.reg 1))) ⟨mem₀, regs2, pos⟩ .normal
      ⟨mem₀, regs3, pos⟩ ((Expr.bin .add (.reg 4) (.reg 1)).size + 1) :=
    runs_assign_iff.mpr ⟨scrPtr, Expr.eval_add (Expr.eval_reg_of_eq (v := arrPtr) (by simp [regs2]))
      (Expr.eval_reg_of_eq (v := m) (by simp [regs2, regs1, s0, startState])) (by omega), rfl, rfl, rfl⟩
  have hr4 : Runs w p ω (.assign 6 (.bin .add (.reg 5) (.reg 1))) ⟨mem₀, regs3, pos⟩ .normal
      ⟨mem₀, regs4, pos⟩ ((Expr.bin .add (.reg 5) (.reg 1)).size + 1) :=
    runs_assign_iff.mpr ⟨hEnd, Expr.eval_add (Expr.eval_reg_of_eq (v := scrPtr) (by simp [regs3]))
      (Expr.eval_reg_of_eq (v := m) (by simp [regs3, regs2, regs1, s0, startState])) (by omega), rfl, rfl, rfl⟩
  -- Copy loop
  obtain ⟨oL, st1, c1, hr_loop, hpost1, hc1⟩ := hloop ⟨mem₀, regs4, pos⟩ ω
    ⟨by simp [regs4, regs3, regs2, regs1, s0, startState],
     by simp [regs4, regs3, regs2, regs1, s0, startState],
     by simp [regs4, regs3, regs2, regs1, s0, startState],
     by simp [regs4, regs3, regs2, regs1], by simp [regs4, regs3, regs2],
     by simp [regs4, regs3], by simp [regs4], by simp,
     fun _ hj => by omega, fun _ _ => rfl⟩
  cases oL with
  | returned _ => cases hpost1
  | normal =>
  obtain ⟨h10, h11, h12, h13, h14, h15, h16, -, hcp1, hfr1⟩ := hpost1
  have hlat1 : ListAt st1.mem arrPtr rawL := fun i hi => hcp1 i hi hi
  -- MergeSort
  obtain ⟨bdMS, hbdMS, oMS, st2, cMS, hrunMS, hpostMS, hcMS⟩ :=
    mergeSort_meetsContract (w := w) (L := rawL) hp hp [arrPtr, m, scrPtr] st1.mem st1.pos ω
      (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> omega)
      ⟨arrPtr, scrPtr, rfl, hw16, by omega, by omega, Or.inl (by omega), hlat1, hraw_w⟩
  obtain ⟨_, _, sortedL, heqMS, _, hperm, hpair, hlat2, hfrMS⟩ := hpostMS
  simp only [List.cons.injEq, and_true] at heqMS
  rcases heqMS with ⟨rfl, -, rfl⟩
  have hsorted_len : sortedL.length = m := hperm.length_eq
  have hsorted_w : ∀ x ∈ sortedL, x < 2 ^ w := fun x hx => hraw_w x (hperm.subset hx)
  set regs5 := Function.update st1.regs 8 oMS.value
  have heArgsMS : evalArgs w st1 [.reg 4, .reg 1, .reg 5] = some [arrPtr, m, scrPtr] :=
    evalArgs_cons (Expr.eval_reg_of_eq h14) <|
    evalArgs_cons (Expr.eval_reg_of_eq h11) <|
    evalArgs_cons (Expr.eval_reg_of_eq h15) <| evalArgs_nil _ _
  have hr_ms : Runs w p ω (.call 8 (bSort + sortIdxMergeSort) [.reg 4, .reg 1, .reg 5])
      st1 .normal ⟨st2.mem, regs5, st2.pos⟩ (argsSize [.reg 4, .reg 1, .reg 5] + cMS + 1) :=
    runs_call_iff.mpr ⟨_, bdMS, oMS, st2, cMS, heArgsMS, hbdMS, hrunMS, rfl, rfl, rfl⟩
  -- Dedup
  obtain ⟨bdDD, hbdDD, oDD, st3, cDD, hrunDD, hpostDD, hcDD⟩ :=
    dedup_meetsContract (w := w) (L := sortedL) hp [arrPtr, sortedL.length, outPtr] st2.mem st2.pos ω
      (by intro a ha; simp at ha; rcases ha with rfl | rfl | rfl <;> omega)
      ⟨arrPtr, outPtr, rfl, hw16, by omega, by omega, Or.inr (by omega), hpair, hlat2, hsorted_w⟩
  obtain ⟨_, _, heqDD, hretDD, -, -, hlat3, hfrDD⟩ := hpostDD
  simp only [List.cons.injEq, and_true] at heqDD
  rcases heqDD with ⟨rfl, -, rfl⟩
  have hT₀_eq : sortedDedup sortedL = T₀ :=
    sortedDedup_perm_eq_finset_sort hperm hpair (fun x => List.mem_toFinset.symm)
  have hT₀_len_le : T₀.length ≤ m := by
    rw [← hT₀_eq, ← hsorted_len]; exact sortedDedup_length_le' sortedL
  set regs6 := Function.update regs5 9 oDD.value
  have heArgsDD : evalArgs w ⟨st2.mem, regs5, st2.pos⟩ [.reg 4, .reg 1, .reg 3] =
      some [arrPtr, sortedL.length, outPtr] :=
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [regs5, h14])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [regs5, h11, hsorted_len])) <|
    evalArgs_cons (Expr.eval_reg_of_eq (by simp [regs5, h13])) <| evalArgs_nil _ _
  have hr_dd : Runs w p ω (.call 9 (bSort + sortIdxDedup) [.reg 4, .reg 1, .reg 3])
      ⟨st2.mem, regs5, st2.pos⟩ .normal ⟨st3.mem, regs6, st3.pos⟩
      (argsSize [.reg 4, .reg 1, .reg 3] + cDD + 1) :=
    runs_call_iff.mpr ⟨_, bdDD, oDD, st3, cDD, heArgsDD, hbdDD, hrunDD, rfl, rfl, rfl⟩
  -- Store `|T₀|` at `h` and return `hEnd`
  set memF := Function.update st3.mem h T₀.length
  have hr_st : Runs w p ω (.store (.reg 2) (.reg 9)) ⟨st3.mem, regs6, st3.pos⟩ .normal
      ⟨memF, regs6, st3.pos⟩ ((Expr.reg 2).size + (Expr.reg 9).size + 1) :=
    runs_store_iff.mpr ⟨h, T₀.length,
      Expr.eval_reg_of_eq (by simp [regs6, regs5, h12]),
      Expr.eval_reg_of_eq (by simp [regs6, hretDD, hT₀_eq]), rfl, rfl, rfl⟩
  have hr_ret : Runs w p ω (.ret (.reg 6)) ⟨memF, regs6, st3.pos⟩ (.returned hEnd)
      ⟨memF, regs6, st3.pos⟩ ((Expr.reg 6).size + 1) :=
    runs_ret_iff.mpr ⟨hEnd, Expr.eval_reg_of_eq (by simp [regs6, regs5, h16]), rfl, rfl, rfl⟩
  have hr_all := runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr1,
    runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr2,
      runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr3,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr4,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_loop,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_ms,
              runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_dd,
                runs_seq_iff.mpr (Or.inr ⟨_, _, _, hr_st, hr_ret, rfl⟩), rfl⟩), rfl⟩), rfl⟩),
          rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hkeep_out : ∀ a, a < h ∨ hEnd ≤ a → memF a = mem₀ a := fun a ha => by
    rw [show memF a = st3.mem a from Function.update_of_ne (by rcases ha with h1 | h2 <;> omega) _ _]
    rw [hfrDD a (by rw [hT₀_eq]; rcases ha with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
    rw [hfrMS a (by rcases ha with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
      (by rcases ha with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)])]
    exact hfr1 a (by rcases ha with h1 | h2 <;> [exact Or.inl (by omega); exact Or.inr (by omega)])
  refine ⟨.returned hEnd, ⟨memF, regs6, st3.pos⟩, _, hr_all, by dsimp [Outcome.value]; omega,
    Function.update_self _ _ _, ?_, Finset.sort_nodup _ _, ?_, hT₀_len_le,
    fun x hx => (hkeep_out x (Or.inr hx)).trans (hz x (by change hEnd ≤ x at hx; omega)),
    fun a ha => hkeep_out a (Or.inl ha), ?_⟩
  · intro i hi
    dsimp only
    rw [show memF (outPtr + i) = st3.mem (outPtr + i) from
      Function.update_of_ne (by omega) _ _]
    rw [hT₀_eq] at hlat3
    exact hlat3 i hi
  · intro v hv
    exact hraw_cap v (List.mem_toFinset.mp ((Finset.mem_sort (· ≤ ·)).mp hv))
  · have hrc : rangeCost (fun _ => 12) 0 m = 12 * m := by simp [rangeCost, Nat.mul_comm]
    dsimp only at hc1
    dsimp only [mergeSortContract, dedupContract] at hcMS hcDD
    have hmEq : rawL.length = m := rfl
    simp only [Expr.size, argsSize, Nat.sub_zero, hrc, hsorted_len, hmEq] at hc1 hcMS hcDD ⊢
    have hlin : 80 * m ≤ 80 * m * (Nat.log 2 (m + 1) + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos _)
    have hdist : 200 * m * (Nat.log 2 (m + 1) + 1) + 80 * m * (Nat.log 2 (m + 1) + 1) =
        280 * m * (Nat.log 2 (m + 1) + 1) := by rw [← Nat.add_mul, ← Nat.add_mul]
    clear * - hc1 hcMS hcDD hlin hdist
    omega

/-- Specialization of `asmFirstBuildRot_runs` to `rawL` whose underlying set is `asmFirstRotSet`:
delivers `OutRotCover` and `T₀.length ≤ 8 * (Enc(U_S) + words + editWords + 1)` directly. -/
theorem asmFirstBuildRot_cover_runs {L w bSort rawPtr vCap h pos words editWords : ℕ} {p : Program}
    (hp : p.HasAt bSort (sortProcs bSort))
    {sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut}
    {tr : BundleTreeState L} {U : List Update} {ord : ℕ → List End} {ed : List OrdEdit}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} (hI : CompLSFInv C_lsst ℓ₀ tr.cs)
    (hBU : tr.cs.G.BatchIsValid U)
    (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    (σ : Rotation (compLSFBatch tr.cs U).G) (hσ : σ.order = applyOrdEdits ord ed)
    (hU_w : 2 * U.length ≤ words) (hed_w : 2 * ed.length ≤ editWords)
    {rawL : List ℕ} {mem₀ : ℕ → ℕ} {ω : ℕ → Bool}
    (hraw_set : rawL.toFinset = asmFirstRotSet sparsify tr U ord ed)
    (hw16 : 16 ≤ 2 ^ w)
    (hraw : ListAt mem₀ rawPtr rawL) (hraw_le : rawPtr + rawL.length ≤ h)
    (hraw_cap : ∀ v ∈ rawL, v < vCap) (hvCap_w : vCap < 2 ^ w)
    (hz : ZeroFrom mem₀ h)
    (hsp : h + 1 + 3 * rawL.length < 2 ^ w) :
    let T₀ := rawL.toFinset.sort (· ≤ ·)
    ∃ o st' c,
      Runs w p ω (asmFirstBuildRotStmt bSort) (startState [rawPtr, rawL.length, h] mem₀ pos) o st' c ∧
      o.value = h + 1 + 3 * rawL.length ∧
      st'.mem h = T₀.length ∧
      ListAt st'.mem (h + 1) T₀ ∧
      T₀.Nodup ∧
      (∀ v ∈ T₀, v < vCap) ∧
      OutRotCover sparsify tr U ord (applyOrdEdits ord ed) T₀ ∧
      T₀.length ≤ 8 * (tr.S_cur.batchEnc (stepBundleTree sparsify tr U ord (applyOrdEdits ord ed)).U_S +
        words + editWords + 1) ∧
      ZeroFrom st'.mem o.value ∧
      (∀ a < h, st'.mem a = mem₀ a) ∧
      c ≤ 280 * rawL.length * (Nat.log 2 (rawL.length + 1) + 1) + 150 := by
  intro T₀
  obtain ⟨o, st', c, hrun, ho, hm, hLA, hnd, hcap, _, hz', hfr, hc⟩ :=
    asmFirstBuildRot_runs hp hw16 hraw hraw_le hraw_cap hvCap_w hz hsp
  have hcov : OutRotCover sparsify tr U ord (applyOrdEdits ord ed) T₀ :=
    asmFirstRotSet_cover (sparsify := sparsify) tr U ord ed hI hBU ρ hρ σ hσ T₀ (fun v hv =>
      (Finset.mem_sort (· ≤ ·)).mpr (hraw_set.symm ▸ hv))
  have hlen : T₀.length ≤ 8 * (tr.S_cur.batchEnc
      (stepBundleTree sparsify tr U ord (applyOrdEdits ord ed)).U_S + words + editWords + 1) := by
    have hcard : T₀.length = (asmFirstRotSet sparsify tr U ord ed).card := by
      simp only [T₀, hraw_set, Finset.length_sort]
    rw [hcard]
    exact asmFirstRotSet_card_le_words sparsify tr U ord ed hU_w hed_w
  exact ⟨o, st', c, hrun, ho, hm, hLA, hnd, hcap, hcov, hlen, hz', hfr, hc⟩

end

/-! ## 2. Interfaces of P2 -/

@[expose] public section

/-- **Interface for P2's tour initialization**: builds `TR vCap eCap` holding
`⟨ord, rf, marks⟩` (with `marks = ∅` initially, or `S₀.E` marked afterwards via `setMark`) from
`OrdListAt mem cOrdPtr ord cWords` and `ExportAt mem fD h rf.F`. -/
structure AsmFirstTourInitAt (TR : ℕ → ℕ → DSRep AsmTourAbs) (w : ℕ) (p : Program)
    (fTourInit : ℕ) where
  mul : ℕ
  space : PolyBound
  runs : ∀ (vCap eCap cOrdPtr cWords fD h : ℕ) (G : MGraph) (ord : ℕ → List End)
      (rf : RootedForest) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      16 ≤ 2 ^ w → vCap < 2 ^ w → eCap < 2 ^ w → h < 2 ^ w →
      G.IsValid → (∀ v ∈ G.V, v < vCap) → (∀ e ∈ G.E, e < eCap) →
      IsRotationOrder G ord →
      OrdListAt mem cOrdPtr ord cWords → cOrdPtr + cWords ≤ h →
      ExportAt mem fD h rf.F → rf.IsRootedSpanningForestOf G →
      ZeroFrom mem h → h + space.eval (vCap + eCap + cWords) < 2 ^ w →
      ∃ body, p.procs[fTourInit]? = some body ∧ ∃ o st' c tx,
        Runs w p ω body (startState [vCap, eCap, cOrdPtr, fD, h] mem pos) o st' c ∧
        (TR vCap eCap).rep h ⟨ord, rf, ∅⟩ tx st'.mem ∧
        (∀ a, (TR vCap eCap).foot h tx a → h ≤ a ∧ a < o.value) ∧
        h < o.value ∧ o.value ≤ h + space.eval (vCap + eCap + cWords) ∧
        ZeroFrom st'.mem o.value ∧
        (∀ a < h, st'.mem a = mem a) ∧
        c + (TR vCap eCap).phi h tx st'.mem ≤ mul * (G.n + G.m + cWords + 1) * ordStoreLog eCap

/-- **Interface for P2's `rootOf` query** (operation `10` of `tourContract`):
writes `a.rf.root v` at `h`, preserving `TR vCap eCap` with cost `≤ mul * ordStoreLog eCap + Δφ`. -/
structure AsmFirstTourRootAt (TR : ℕ → ℕ → DSRep AsmTourAbs) (w : ℕ) (p : Program)
    (fRootOf : ℕ) where
  mul : ℕ
  querySpace : ℕ
  querySpace_ge : 1 ≤ querySpace
  runs : ∀ (vCap eCap tourH v h : ℕ) (a : AsmTourAbs) (tx : (TR vCap eCap).τ)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      tourH < 2 ^ w → v < vCap → v < 2 ^ w → h < 2 ^ w →
      (TR vCap eCap).rep tourH a tx mem → (∀ x, (TR vCap eCap).foot tourH tx x → x < h) →
      ZeroFrom mem h → h + querySpace < 2 ^ w →
      ∃ body, p.procs[fRootOf]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, v, h] mem pos) o st' c ∧
        (TR vCap eCap).rep tourH a tx' st'.mem ∧
        st'.mem h = a.rf.root v ∧
        h + 1 ≤ o.value ∧
        (TR vCap eCap).Respects ((TR vCap eCap).foot tourH tx) h querySpace mem o.value tourH tx' st'.mem ∧
        c + (TR vCap eCap).phi tourH tx' st'.mem ≤ mul * ordStoreLog eCap + (TR vCap eCap).phi tourH tx mem

/-- **Interface for P2's bundle-tour projection** to P5:
exposes P5's three read-only queries (`idxList`, `idxLen`, `idxOwner`) on `asmTourCordView` of `TR`. -/
def AsmFirstTourBundleProj (TS : BundleTourSpec) (TR : ℕ → ℕ → DSRep AsmTourAbs) (w : ℕ)
    (p : Program) (idxList idxLen idxOwner : ℕ) : Prop :=
  ∀ (vCap eCap : ℕ) (vo : ℕ → List End) (vf : RootedForest) (vc : ℕ → List End) (mk : Finset End),
    ∃ T : BundleTourAt TS w vCap eCap p idxList idxLen idxOwner,
      T.rep = asmTourCordView (TR vCap eCap) vo vf vc mk

end

end MinCostFlow.SparseCore.Program
