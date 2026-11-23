module

public import MinCostFlow.SparseCore.Program.AssemblyFirstRotProg
public import MinCostFlow.SparseCore.Program.AssemblyFirstTourPot
public import MinCostFlow.SparseCore.Program.TourAsmBridge

import Mathlib.Tactic

/-!
# Tour facts proved from P2 (`AssemblyFirstTourFacts`)

Discharges the tour facts provable directly from `tourDS_implements` (`TourDS.lean`) and
`TourAsmBridge.lean`, both for `tourAsmRep` and for its potential
wrapper `asmTourRepWithPot tourAsmRep cPot`:

1. **`AsmFirstTourBundleProj`** (`tourAsmRep_bundleProj`, `tourAsmRepWithPot_bundleProj`):
   proved directly from `tourDS_asmBrTourBridge` (`TourAsmBridge.lean`) and
   `asmTourRepWithPot_bundleBridge` (`AssemblyFirstTourPot.lean`).
2. **Operation `10` (`rootOf` on an end key) vs `AsmFirstTourRootAt` (vertex query):**
   - `tourContract` operation `10` (`tourOp b 10`) takes an **end key** `keyX` with
     `∃ u, endOfKey keyX ∈ s.ord u` and writes `s.rf.root (ordSrc s.ord (endOfKey keyX))` at `h`
     (`AsmFirstTourEndRootAt`, proved in `tourAsmRep_endRootAt` and `tourAsmRepWithPot_endRootAt`
     directly from `tourDS_implements` / `tourOp_rootOf_exact_runs`).
   - `AsmFirstTourRootAt` (`AssemblyFirstRotProg.lean`) takes a **vertex** `v < vCap`, so
     `tourOp b 10` does not satisfy `AsmFirstTourRootAt` directly. Instead, the 8-line
     deterministic wrapper `asmFirstTourVertRootStmt (tourOp b 10)` reads `firstEnd[v]` (returning
     `v` directly when `a.ord v = []`, since `v` is then isolated in `a.rf.F`) and otherwise reads
     `keyOfNode[firstEnd[v]]` and calls `tourOp b 10`, proving `AsmFirstTourRootAt` for both
     `tourAsmRep` (`asmFirstTourVertRoot_runs`) and `asmTourRepWithPot`
     (`asmFirstTourVertRoot_withPot_runs`).
3. **`O(1)` concrete readout lemmas on `tourAsmRep`** (`tourAsmRep_isRoot_read`,
   `tourAsmRep_isOpen_read`) used by the block-by-block tour step driver.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore
open MinCostFlow.DynSpanner.Program

/-! ## 1. `AsmFirstTourBundleProj` for `tourAsmRep` and `asmTourRepWithPot` -/

public section

/-- `tourProcs b` satisfies `AsmFirstTourBundleProj tourBundleSpec tourAsmRep` directly from
`tourDS_asmBrTourBridge` (`TourAsmBridge.lean`). -/
theorem tourAsmRep_bundleProj (w b : ℕ) (p : Program) (hp : HasTourProcs p b) :
    AsmFirstTourBundleProj tourBundleSpec tourAsmRep w p
      (tourOp b 4) (tourOp b 12) (tourOp b 10) :=
  tourDS_asmBrTourBridge w b p hp

/-- `tourProcs b` satisfies `AsmFirstTourBundleProj` on `asmTourRepWithPot tourAsmRep cPot`. -/
theorem tourAsmRepWithPot_bundleProj (w b : ℕ) (p : Program) (hp : HasTourProcs p b)
    (cPot : ℕ → ℕ) :
    AsmFirstTourBundleProj tourBundleSpec (asmTourRepWithPot tourAsmRep cPot) w p
      (tourOp b 4) (tourOp b 12) (tourOp b 10) :=
  asmTourRepWithPot_bundleBridge (tourDS_asmBrTourBridge w b p hp) cPot

end

/-! ## 2. Operation `10` (`AsmFirstTourEndRootAt`) and vertex wrapper (`AsmFirstTourRootAt`) -/

@[expose] public section

/-- **End-key `rootOf` interface** matching operation `10` of `tourContract` (`tourOp b 10`):
given an active end key `keyX` (`∃ u, endOfKey keyX ∈ a.ord u`), writes
`a.rf.root (ordSrc a.ord (endOfKey keyX))` at `h` with exact space `1` (`o.value = h + 1`). -/
structure AsmFirstTourEndRootAt (TR : ℕ → ℕ → DSRep AsmTourAbs) (w : ℕ) (p : Program)
    (fEndRoot : ℕ) where
  mul : ℕ
  querySpace : ℕ
  querySpace_ge : 1 ≤ querySpace
  runs : ∀ (vCap eCap tourH keyX h : ℕ) (a : AsmTourAbs) (tx : (TR vCap eCap).τ)
      (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      tourH < 2 ^ w → keyX < 2 * eCap → keyX < 2 ^ w → h < 2 ^ w →
      (∃ u, endOfKey keyX ∈ a.ord u) →
      (TR vCap eCap).rep tourH a tx mem →
      (∀ x, (TR vCap eCap).foot tourH tx x → x < h) →
      ZeroFrom mem h → h + querySpace < 2 ^ w →
      ∃ body, p.procs[fEndRoot]? = some body ∧ ∃ o st' c tx',
        Runs w p ω body (startState [tourH, keyX, h] mem pos) o st' c ∧
        (TR vCap eCap).rep tourH a tx' st'.mem ∧
        st'.mem h = a.rf.root (ordSrc a.ord (endOfKey keyX)) ∧
        o.value = h + 1 ∧
        (TR vCap eCap).Respects ((TR vCap eCap).foot tourH tx) h querySpace mem o.value tourH tx' st'.mem ∧
        c + (TR vCap eCap).phi tourH tx' st'.mem ≤
          mul * ordStoreLog eCap + (TR vCap eCap).phi tourH tx mem

/-- Deterministic vertex-to-root query `[tourH, v, h]` wrapping `fEndRoot` (`tourOp b 10`):
reads `u := firstEnd[v]`; if `u = 0` (`a.ord v = []`), `v` is isolated in `a.rf.F` so
`a.rf.root v = v`; otherwise reads `keyX := keyOfNode[u]` and calls `fEndRoot [tourH, keyX, h]`. -/
def asmFirstTourVertRootStmt (fEndRoot : ℕ) : Stmt :=
  .assign 3 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))) ;;
  .assign 4 (.load (.bin .add (.reg 3) (.reg 1))) ;;
  .cond (.bin .eq (.reg 4) (.const 0))
    (.store (.reg 2) (.reg 1) ;;
     .ret (.bin .add (.reg 2) (.const 1)))
    (.assign 5 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
     .assign 6 (.load (.bin .add (.reg 5) (.reg 4))) ;;
     .call 7 fEndRoot [.reg 0, .reg 6, .reg 2] ;;
     .ret (.reg 7))

end

public section

theorem asmFirstTourVertRootStmt_noRand (fEndRoot : ℕ) :
    (asmFirstTourVertRootStmt fEndRoot).NoRand := by
  simp [asmFirstTourVertRootStmt, Stmt.NoRand]

/-- **Operation `10` (`tourOp b 10`) directly satisfies `AsmFirstTourEndRootAt`** for `tourAsmRep`,
with `mul = tourMul` and `querySpace = 1`. -/
@[expose] def tourAsmRep_endRootAt (w b : ℕ) (p : Program) (hp : HasTourProcs p b) :
    AsmFirstTourEndRootAt tourAsmRep w p (tourOp b 10) where
  mul := tourMul
  querySpace := 1
  querySpace_ge := le_refl 1
  runs := fun vCap eCap tourH keyX h a tx mem pos ω _ _ _ _ hact hrep hfoot hz hsp => by
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH (asmTourToTour a) tx mem at hrep
    have ⟨_, hw2⟩ := tourDS_wide_of_foot hrep hfoot hsp
    let C := hp.toSplayCore (w := w) (by omega)
    obtain ⟨o, st', c, hrun, hval', x', hrep', hans, hz', hfr', hft', hcost⟩ :=
      tourOp_rootOf_exact_runs (pos := pos) (ordStoreRep_local vCap eCap) C ω hrep hact hfoot hz hsp
    refine ⟨_, hp.op10_body, o, st', c, x', hrun, hrep', hans, hval',
      ⟨by omega, by omega, hz', hfr', fun a' ha' => Or.inl (hft' a' ha')⟩, ?_⟩
    rw [ordStoreLog_eq_tourLog]
    have hmono := Nat.mul_le_mul_right (tourLog eCap) tourMul_ge_query
    dsimp only [tourAsmRep, tourDSRep] at hcost ⊢
    omega

/-- Lifts `AsmFirstTourEndRootAt` from `TR` to `asmTourRepWithPot TR cPot`. -/
@[expose] def asmTourRepWithPot_endRootAt {TR : ℕ → ℕ → DSRep AsmTourAbs} {w : ℕ} {p : Program}
    {fEndRoot : ℕ} (H : AsmFirstTourEndRootAt TR w p fEndRoot) (cPot : ℕ → ℕ) :
    AsmFirstTourEndRootAt (asmTourRepWithPot TR cPot) w p fEndRoot where
  mul := H.mul
  querySpace := H.querySpace
  querySpace_ge := H.querySpace_ge
  runs := fun vCap eCap tourH keyX h a tx mem pos ω h1 h2 h3 h4 hact ⟨hr, hp⟩ hfoot hz hsp => by
    obtain ⟨body, hbody, o, st', c, tx', hrun, hrep', hans, hval', hresp', hcost'⟩ :=
      H.runs vCap eCap tourH keyX h a tx.1 mem pos ω h1 h2 h3 h4 hact hr hfoot hz hsp
    refine ⟨body, hbody, o, st', c, (tx', tx.2), hrun, ⟨hrep', hp⟩, hans, hval', hresp', ?_⟩
    dsimp [asmTourRepWithPot] at hcost' ⊢; omega

/-- `tourOp b 10` satisfies `AsmFirstTourEndRootAt` on `asmTourRepWithPot tourAsmRep cPot`. -/
@[expose] def tourAsmRepWithPot_endRootAt (w b : ℕ) (p : Program) (hp : HasTourProcs p b)
    (cPot : ℕ → ℕ) :
    AsmFirstTourEndRootAt (asmTourRepWithPot tourAsmRep cPot) w p (tourOp b 10) :=
  asmTourRepWithPot_endRootAt (tourAsmRep_endRootAt w b p hp) cPot

/-- The root query of an end in `tourAsmRepWithPot_endRootAt` uses one cell. -/
theorem tourAsmRepWithPot_endRootAt_querySpace (w b : ℕ) (p : Program) (hp : HasTourProcs p b)
    (cPot : ℕ → ℕ) : (tourAsmRepWithPot_endRootAt w b p hp cPot).querySpace = 1 :=
  rfl

/-- The multiplier of `tourAsmRepWithPot_endRootAt` is `tourMul`. -/
theorem tourAsmRepWithPot_endRootAt_mul (w b : ℕ) (p : Program) (hp : HasTourProcs p b)
    (cPot : ℕ → ℕ) : (tourAsmRepWithPot_endRootAt w b p hp cPot).mul = tourMul :=
  rfl

private lemma isolated_root_eq_self {vCap eCap v : ℕ} {s : TourAbs}
    (hv : TourValid vCap eCap s) (hord : s.ord v = []) :
    s.rf.root v = v := by
  have hconn_eq : ∀ r, s.rf.F.Connected v r → r = v := by
    rintro r ⟨P, hP⟩
    cases P with
    | nil =>
      cases hP
      rfl
    | cons x xs =>
      cases hP with
      | cons he hsrc _ =>
        have hx : x ∈ s.ord (s.rf.F.src x) := hv.compat.mem_ord_of_forest he
        rw [hsrc, hord] at hx
        cases hx
  unfold RootedForest.root
  split_ifs with h
  · exact hconn_eq _ h.choose_spec.2
  · rfl

/-- **Verification of `asmFirstTourVertRootStmt (tourOp b 10)`**: satisfies `AsmFirstTourRootAt`
for `tourAsmRep` with `mul = tourMul + 40` and `querySpace = 1`. -/
@[expose] def asmFirstTourVertRoot_runs (w b fVertRoot : ℕ) (p : Program)
    (hp : HasTourProcs p b)
    (hf : p.procs[fVertRoot]? = some (asmFirstTourVertRootStmt (tourOp b 10))) :
    AsmFirstTourRootAt tourAsmRep w p fVertRoot where
  mul := tourMul + 40
  querySpace := 1
  querySpace_ge := le_refl 1
  runs := fun vCap eCap tourH v h a tx mem pos ω htourW hvCap hvW hhW hrep hfoot hz hsp => by
    change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH (asmTourToTour a) tx mem at hrep
    have hord_le : ordHandleOf tourH vCap eCap ≤ h := hrep.fixed_le_heap hfoot
    have hwide : 18 ≤ 2 ^ w := by simp [ordHandleOf, tourFixedSize] at hord_le; omega
    have htl : 1 ≤ ordStoreLog eCap := by rw [ordStoreLog_eq_tourLog]; simp [tourLog]
    have hhdr := hrep.header
    set s0 := startState [tourH, v, h] mem pos
    set feBase := firstEndBase tourH
    set u := mem (feBase + v)
    set r1 := Function.update s0.regs 3 feBase
    set r2 := Function.update r1 4 u
    have ha1 : Runs w p ω (.assign 3 (.load (.bin .add (.reg 0) (.const HDR_FIRST_END))))
        s0 .normal ⟨mem, r1, pos⟩ 5 :=
      runs_assign_iff.mpr ⟨feBase,
        Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := tourH) (by simp [s0, startState]))
            (Expr.eval_const (by simp [HDR_FIRST_END]; omega))
            (by simp [HDR_FIRST_END, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
          hhdr.2.2.2.2.1, rfl, rfl, rfl⟩
    have ha2 : Runs w p ω (.assign 4 (.load (.bin .add (.reg 3) (.reg 1))))
        ⟨mem, r1, pos⟩ .normal ⟨mem, r2, pos⟩ 5 :=
      runs_assign_iff.mpr ⟨u,
        Expr.eval_load_of_eq
          (Expr.eval_add (Expr.eval_reg_of_eq (v := feBase) (by simp [r1]))
            (Expr.eval_reg_of_eq (v := v) (by simp [r1, s0, startState]))
            (by simp only [feBase, firstEndBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
          rfl, rfl, rfl, rfl⟩
    have hfe_eq := hrep.firstEnd_mem v hvCap
    by_cases hu0 : u = 0
    · have hordNil : a.ord v = [] := by
        cases hhd : a.ord v with
        | nil => rfl
        | cons e es =>
          have hmem : e ∈ a.ord v := by simp [hhd]
          have hne := (hrep.active_end v hvCap e hmem).1
          simp only [asmTourToTour, hhd, List.head?_cons] at hfe_eq
          exact absurd (hu0 ▸ hfe_eq.symm) hne
      have hrootV : a.rf.root v = v := isolated_root_eq_self hrep.valid hordNil
      have hcond : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r2, pos⟩ = some 1 := by
        simp [Expr.eval, r2, hu0, BinOp.eval, (by omega : 0 < 2 ^ w), (by omega : 1 < 2 ^ w)]
      set mem1 := Function.update mem h v
      have hst : Runs w p ω (.store (.reg 2) (.reg 1)) ⟨mem, r2, pos⟩ .normal ⟨mem1, r2, pos⟩ 3 :=
        runs_store_iff.mpr ⟨h, v, by simp [Expr.eval, r2, r1, s0, startState],
          by simp [Expr.eval, r2, r1, s0, startState], rfl, rfl, rfl⟩
      have hret : Runs w p ω (.ret (.bin .add (.reg 2) (.const 1))) ⟨mem1, r2, pos⟩
          (.returned (h + 1)) ⟨mem1, r2, pos⟩ 4 :=
        runs_ret_iff.mpr ⟨h + 1, by
          simp [Expr.eval, r2, r1, s0, startState, BinOp.eval, (by omega : 1 < 2 ^ w), hsp],
          rfl, rfl, rfl⟩
      have hrunCond : Runs w p ω
          (.cond (.bin .eq (.reg 4) (.const 0))
            (.store (.reg 2) (.reg 1) ;; .ret (.bin .add (.reg 2) (.const 1)))
            (.assign 5 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
             .assign 6 (.load (.bin .add (.reg 5) (.reg 4))) ;;
             .call 7 (tourOp b 10) [.reg 0, .reg 6, .reg 2] ;;
             .ret (.reg 7)))
          ⟨mem, r2, pos⟩ (.returned (h + 1)) ⟨mem1, r2, pos⟩ (3 + (3 + 4 + 1) + 1) :=
        runs_cond_iff.mpr ⟨1, 3 + 4 + 1, hcond, by
          simpa using runs_seq_iff.mpr (Or.inr ⟨_, _, _, hst, hret, rfl⟩), rfl⟩
      have hrunAll := runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha1,
        runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha2, hrunCond, rfl⟩), rfl⟩)
      have hloc := tourAsmRep_local vCap eCap tourH a tx mem mem1 fun a' ha' =>
        (Function.update_of_ne (Nat.ne_of_lt (hfoot a' ha')) _ _).symm
      refine ⟨_, hf, .returned (h + 1), ⟨mem1, r2, pos⟩, _, tx, hrunAll, hloc.1 hrep,
        by simp [mem1, hrootV], by simp [Outcome.value],
        ⟨by simp [Outcome.value], by simp [Outcome.value],
          fun a' ha' => by
            simp only [Outcome.value] at ha'
            dsimp only [mem1]
            rw [Function.update_of_ne (by omega)]
            exact hz a' (by omega),
          fun a' ha' _ => Function.update_of_ne (Nat.ne_of_lt ha') _ _,
          fun _ ha' => Or.inl ha'⟩, ?_⟩
      rw [← hloc.2]
      have hle : 40 ≤ (tourMul + 40) * ordStoreLog eCap :=
        le_trans (by omega : 40 ≤ tourMul + 40) (Nat.le_mul_of_pos_right _ htl)
      omega
    · cases hhd : a.ord v with
      | nil =>
        simp only [asmTourToTour, hhd, List.head?_nil] at hfe_eq
        exact absurd hfe_eq hu0
      | cons e es =>
        have he_mem : e ∈ a.ord v := by simp [hhd]
        have hu_eq : u = tx.nodeOf (endKey e) := by
          simpa [asmTourToTour, hhd] using hfe_eq
        have he_lt : e.1 < eCap := hrep.valid.ordWithin.2.2 v e he_mem
        have hke_lt : endKey e < 2 * eCap := by
          cases e with | mk e1 b1 => cases b1 <;> simp [endKey] at he_lt ⊢ <;> omega
        have hu_le : u ≤ tx.numNodes := by rw [hu_eq]; exact (hrep.nodeOf_mem _ hke_lt).2
        have hu_pos : 1 ≤ u := by omega
        have hkey_mem := hrep.keyOf_mem u hu_pos hu_le
        have hkey_eq : tx.keyOf u = endKey e := by
          rw [hu_eq]; exact hrep.nodeOf_keyOf _ hke_lt (hu_eq ▸ hu0)
        set konBase := keyOfNodeBase tourH vCap eCap
        set keyX := endKey e
        set r3 := Function.update r2 5 konBase
        set r4 := Function.update r3 6 keyX
        have ha3 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))))
            ⟨mem, r2, pos⟩ .normal ⟨mem, r3, pos⟩ 5 :=
          runs_assign_iff.mpr ⟨konBase,
            Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (v := tourH) (by simp [r2, r1, s0, startState]))
                (Expr.eval_const (by simp [HDR_KEY_OF_NODE]; omega))
                (by simp [HDR_KEY_OF_NODE, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
              hhdr.2.2.2.2.2.2.2.2.1, rfl, rfl, rfl⟩
        have ha4 : Runs w p ω (.assign 6 (.load (.bin .add (.reg 5) (.reg 4))))
            ⟨mem, r3, pos⟩ .normal ⟨mem, r4, pos⟩ 5 :=
          runs_assign_iff.mpr ⟨keyX,
            Expr.eval_load_of_eq
              (Expr.eval_add (Expr.eval_reg_of_eq (v := konBase) (by simp [r3]))
                (Expr.eval_reg_of_eq (v := u) (by simp [r3, r2]))
                (by have := hrep.numNodes_le; simp only [konBase, keyOfNodeBase, ordHandleOf, tourFixedSize] at hord_le ⊢; omega))
              (hkey_mem.1.trans hkey_eq), rfl, rfl, rfl⟩
        have hact : ∃ u', endOfKey keyX ∈ a.ord u' := ⟨v, by rw [endOfKey_endKey']; exact he_mem⟩
        have hsrc : ordSrc a.ord (endOfKey keyX) = v := by
          rw [endOfKey_endKey']; exact hrep.valid.compat.ordSrc_eq he_mem
        have hkeyW : keyX < 2 ^ w := by
          simp only [ordHandleOf, tourFixedSize] at hord_le; omega
        obtain ⟨bd10, hbd10, o10, st10, c10, tx', hrun10, hrep', hans, hval10, hresp10, hcost10⟩ :=
          (tourAsmRep_endRootAt w b p hp).runs vCap eCap tourH keyX h a tx mem pos ω
            htourW hke_lt hkeyW hhW hact hrep hfoot hz hsp
        have heArgs : evalArgs w ⟨mem, r4, pos⟩ [.reg 0, .reg 6, .reg 2] = some [tourH, keyX, h] :=
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [r4, r3, r2, r1, s0, startState])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [r4])) <|
          evalArgs_cons (Expr.eval_reg_of_eq (by simp [r4, r3, r2, r1, s0, startState])) <|
          evalArgs_nil _ _
        set r5 := Function.update r4 7 o10.value
        have hcall10 : Runs w p ω (.call 7 (tourOp b 10) [.reg 0, .reg 6, .reg 2])
            ⟨mem, r4, pos⟩ .normal ⟨st10.mem, r5, st10.pos⟩
            (argsSize [.reg 0, .reg 6, .reg 2] + c10 + 1) :=
          runs_call_iff.mpr ⟨_, bd10, o10, st10, c10, heArgs, hbd10, hrun10, rfl, rfl, rfl⟩
        have hret10 : Runs w p ω (.ret (.reg 7)) ⟨st10.mem, r5, st10.pos⟩
            (.returned o10.value) ⟨st10.mem, r5, st10.pos⟩ 2 :=
          runs_ret_iff.mpr ⟨o10.value, Expr.eval_reg_of_eq (by simp [r5]), rfl, rfl, rfl⟩
        have hcond0 : (Expr.bin .eq (.reg 4) (.const 0)).eval w ⟨mem, r2, pos⟩ = some 0 := by
          simp [Expr.eval, r2, hu0, BinOp.eval, (by omega : 0 < 2 ^ w)]
        have hrunElse := runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha3,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha4,
            runs_seq_iff.mpr (Or.inr ⟨_, _, _, hcall10, hret10, rfl⟩), rfl⟩), rfl⟩)
        have hrunCond : Runs w p ω
            (.cond (.bin .eq (.reg 4) (.const 0))
              (.store (.reg 2) (.reg 1) ;; .ret (.bin .add (.reg 2) (.const 1)))
              (.assign 5 (.load (.bin .add (.reg 0) (.const HDR_KEY_OF_NODE))) ;;
               .assign 6 (.load (.bin .add (.reg 5) (.reg 4))) ;;
               .call 7 (tourOp b 10) [.reg 0, .reg 6, .reg 2] ;;
               .ret (.reg 7)))
            ⟨mem, r2, pos⟩ (.returned o10.value) ⟨st10.mem, r5, st10.pos⟩ _ :=
          runs_cond_iff.mpr ⟨0, _, hcond0, by simpa using hrunElse, rfl⟩
        have hrunAll := runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha1,
          runs_seq_iff.mpr (Or.inr ⟨_, _, _, ha2, hrunCond, rfl⟩), rfl⟩)
        refine ⟨_, hf, .returned o10.value, ⟨st10.mem, r5, st10.pos⟩, _, tx', hrunAll, hrep',
          by rw [hans, hsrc], by change h + 1 ≤ o10.value; omega,
          by simpa [Outcome.value, tourAsmRep_endRootAt] using hresp10, ?_⟩
        simp only [Expr.size, tourAsmRep_endRootAt] at hcost10 ⊢
        have h40 : 40 ≤ 40 * ordStoreLog eCap := Nat.le_mul_of_pos_right 40 htl
        have hdist : (tourMul + 40) * ordStoreLog eCap =
            tourMul * ordStoreLog eCap + 40 * ordStoreLog eCap := Nat.add_mul _ _ _
        omega

/-- Lifts `AsmFirstTourRootAt` from `TR` to `asmTourRepWithPot TR cPot`. -/
@[expose] def asmTourRepWithPot_rootAt {TR : ℕ → ℕ → DSRep AsmTourAbs} {w : ℕ} {p : Program}
    {fRootOf : ℕ} (H : AsmFirstTourRootAt TR w p fRootOf) (cPot : ℕ → ℕ) :
    AsmFirstTourRootAt (asmTourRepWithPot TR cPot) w p fRootOf where
  mul := H.mul
  querySpace := H.querySpace
  querySpace_ge := H.querySpace_ge
  runs := fun vCap eCap tourH v h a tx mem pos ω h1 h2 h3 h4 ⟨hr, hp⟩ hfoot hz hsp => by
    obtain ⟨body, hbody, o, st', c, tx', hrun, hrep', hans, hlo, hresp', hcost'⟩ :=
      H.runs vCap eCap tourH v h a tx.1 mem pos ω h1 h2 h3 h4 hr hfoot hz hsp
    refine ⟨body, hbody, o, st', c, (tx', tx.2), hrun, ⟨hrep', hp⟩, hans, hlo, hresp', ?_⟩
    dsimp [asmTourRepWithPot] at hcost' ⊢; omega

/-- `asmFirstTourVertRootStmt (tourOp b 10)` satisfies `AsmFirstTourRootAt` on
`asmTourRepWithPot tourAsmRep cPot`. -/
@[expose] def asmFirstTourVertRoot_withPot_runs (w b fVertRoot : ℕ) (p : Program)
    (hp : HasTourProcs p b)
    (hf : p.procs[fVertRoot]? = some (asmFirstTourVertRootStmt (tourOp b 10))) (cPot : ℕ → ℕ) :
    AsmFirstTourRootAt (asmTourRepWithPot tourAsmRep cPot) w p fVertRoot :=
  asmTourRepWithPot_rootAt (asmFirstTourVertRoot_runs w b fVertRoot p hp hf) cPot

/-- The root query of `asmFirstTourVertRoot_withPot_runs` uses one cell. -/
theorem asmFirstTourVertRoot_withPot_runs_querySpace (w b fVertRoot : ℕ) (p : Program)
    (hp : HasTourProcs p b)
    (hf : p.procs[fVertRoot]? = some (asmFirstTourVertRootStmt (tourOp b 10))) (cPot : ℕ → ℕ) :
    (asmFirstTourVertRoot_withPot_runs w b fVertRoot p hp hf cPot).querySpace = 1 :=
  rfl

/-- The multiplier of `asmFirstTourVertRoot_withPot_runs` is `tourMul + 40`. -/
theorem asmFirstTourVertRoot_withPot_runs_mul (w b fVertRoot : ℕ) (p : Program)
    (hp : HasTourProcs p b)
    (hf : p.procs[fVertRoot]? = some (asmFirstTourVertRootStmt (tourOp b 10))) (cPot : ℕ → ℕ) :
    (asmFirstTourVertRoot_withPot_runs w b fVertRoot p hp hf cPot).mul = tourMul + 40 :=
  rfl

/-! ## 3. `O(1)` concrete readout lemmas on `tourAsmRep` -/

/-- Under `tourAsmRep`, `mem (mem (tourH + HDR_IS_ROOT) + v)` equals `1` iff `v ∈ a.rf.R`. -/
theorem tourAsmRep_isRoot_read {vCap eCap tourH v : ℕ} {a : AsmTourAbs}
    {tx : (tourAsmRep vCap eCap).τ} {mem : ℕ → ℕ}
    (h : (tourAsmRep vCap eCap).rep tourH a tx mem) (hv : v < vCap) :
    mem (tourH + HDR_IS_ROOT) = isRootBase tourH vCap ∧
    mem (isRootBase tourH vCap + v) = if v ∈ a.rf.R then 1 else 0 := by
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH (asmTourToTour a) tx mem at h
  exact ⟨h.header.2.2.2.2.2.1, h.isRoot_mem v hv⟩

/-- Under `tourAsmRep`, for any active edge `e` (`(e, true) ∈ a.ord v`), reading `nodeOf[2 * e]`
and its `isOpen` payload word (`nodesBase + 17 * u + 9`) gives `1` iff `e ∉ a.rf.F.E`. -/
theorem tourAsmRep_isOpen_read {vCap eCap tourH e v : ℕ} {a : AsmTourAbs}
    {tx : (tourAsmRep vCap eCap).τ} {mem : ℕ → ℕ}
    (h : (tourAsmRep vCap eCap).rep tourH a tx mem)
    (hv : v < vCap) (he : (e, true) ∈ a.ord v) :
    let u := tx.nodeOf (2 * e)
    mem (tourH + HDR_NODE_OF_END) = nodeOfEndBase tourH vCap ∧
    mem (nodeOfEndBase tourH vCap + 2 * e) = u ∧
    1 ≤ u ∧ u ≤ tx.numNodes ∧
    mem (tourH + HDR_NODES_BASE) = nodesBase tourH vCap eCap ∧
    mem (nodesBase tourH vCap eCap + 17 * u + 9) = if e ∉ a.rf.F.E then 1 else 0 := by
  change TourRepAt (ordStoreRep vCap eCap) vCap eCap tourH (asmTourToTour a) tx mem at h
  have he_lt : e < eCap := h.valid.ordWithin.2.2 v (e, true) he
  have h2e_lt : 2 * e < 2 * eCap := by omega
  have hne : tx.nodeOf (2 * e) ≠ 0 := by
    simpa [endKey] using (h.active_end v hv (e, true) he).1
  have ⟨hnm, hle⟩ := h.nodeOf_mem (2 * e) h2e_lt
  have hu1 : 1 ≤ tx.nodeOf (2 * e) := Nat.pos_of_ne_zero hne
  have hkey : tx.keyOf (tx.nodeOf (2 * e)) = 2 * e := h.nodeOf_keyOf (2 * e) h2e_lt hne
  have hval := h.val_active (tx.nodeOf (2 * e)) hu1 hle
    ⟨v, by rw [hkey, tour_endOfKey_two_mul]; exact he⟩
  have hopen := nodesAt_isOpen h.nodesAt hle
  rw [hval, hkey, tour_endOfKey_two_mul] at hopen
  refine ⟨h.header.2.2.2.2.2.2.1, hnm, hu1, hle, h.header.2.2.2.2.2.2.2.2.2.2.2.2.1, ?_⟩
  by_cases hE : e ∈ a.rf.F.E <;> simpa [asmTourToTour, hE] using hopen

end

end MinCostFlow.SparseCore.Program
