module

public import MinCostFlow.MinRatio.InitFullAssembly
public import MinCostFlow.MinRatio.FreshTables
public import MinCostFlow.MinRatio.PathTreeCall
import MinCostFlow.MinRatio.InitLevels

/-!
# Post-levels Algorithm 2 Init tail

After `buildSolverInitLevels` constructs all `d` sparse cores and the terminal
level of Algorithm 1 (page 20), Algorithm 2 (page 29) reserves its zeroed
schedule and counter arrays, initializes the identity fresh-name tables,
initializes the Section 6 path tree, stores the Detect header descriptors in
the shared handle, and returns the new free heap pointer.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- For a nonempty connected instance `I`, the initial fresh edge-ID counter
`G.E.sup id + 1` in `algorithm2_init` equals `I.m`. -/
theorem namedInstance_nextFresh (I : Instance) (hm : 0 < I.m) :
    (IPM.namedInstance I).E.sup id + 1 = I.m := by
  have hE : (IPM.namedInstance I).E = Finset.range I.m := rfl
  rw [hE]
  cases h : I.m with
  | zero => omega
  | succ k =>
    have hsup : (Finset.range (k + 1)).sup id = k := by
      apply le_antisymm
      · exact Finset.sup_le fun e he => Nat.le_of_lt_succ (Finset.mem_range.mp he)
      · exact Finset.le_sup (f := id) (Finset.mem_range.mpr (Nat.lt_succ_self k))
    rw [hsup]

/-- `buildSolverInitLevels` leaves every register `r ≥ 55` other than `77`
unchanged, preserving the handle (`74`), depth (`75`), root graph (`69`),
lengths (`71`), gradients (`70`), limbs (`67`), and precision (`68`). -/
theorem buildSolverInitLevels_preserves_regs
    {w init read forestOp copy sort cell terminalInit r cost : ℕ}
    {p : Program} {ω : ℕ → Bool} {st out : State}
    (hr : 55 ≤ r) (h77 : r ≠ 77)
    (hrun : Runs w p ω (buildSolverInitLevels init read forestOp copy sort cell terminalInit)
      st .normal out cost) :
    out.regs r = st.regs r := by
  unfold buildSolverInitLevels at hrun
  rcases runs_seq_iff.mp hrun with ⟨_, _, _, hbad, _⟩ | ⟨mid, _, _, hprep, hsuf, _⟩
  · cases hbad
  have h1 : out.regs r = mid.regs r :=
    runs_preserves_above hr (rebuildChainSuffix_writesBelow ..) hsuf
  unfold prepareSolverInitLevels at hprep
  rcases runs_seq_iff.mp hprep with ⟨_, _, _, hbad, _⟩ | ⟨mid1, _, _, hres, hstg, _⟩
  · cases hbad
  have h2 : mid.regs r = mid1.regs r := by
    unfold stageSolverInitLevels at hstg
    exact runs_preserves_above hr (by rfl) hstg
  have h3 : mid1.regs r = st.regs r := by
    unfold reserveSolverInitLevelTables at hres
    rcases runs_seq_iff.mp hres with ⟨_, _, _, hbad, _⟩ | ⟨a1, _, _, ha1, hrest1, _⟩
    · cases hbad
    rcases runs_seq_iff.mp hrest1 with ⟨_, _, _, hbad, _⟩ | ⟨a2, _, _, ha2, ha3, _⟩
    · cases hbad
    obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp ha1
    obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp ha2
    obtain ⟨_, _, _, rfl, _⟩ := runs_assign_iff.mp ha3
    simp [Function.update_of_ne (show r ≠ 51 by omega),
      Function.update_of_ne (show r ≠ 52 by omega), Function.update_of_ne h77]
  exact h1.trans (h2.trans h3)

/-- Populate the identity forward and inverse fresh-name arrays on `0 .. m - 1`
using base pointers in registers `81` and `82` and length `m` in register `84`. -/
@[expose] def initFreshIdentityTables : Stmt :=
  forRange 0 (.const 0) (.reg 84)
    (.store (.bin .add (.reg 81) (.reg 0)) (.reg 0) ;;
     .store (.bin .add (.reg 82) (.reg 0)) (.reg 0))

theorem initFreshIdentityTables_noRand : initFreshIdentityTables.NoRand := by
  simp [initFreshIdentityTables, forRange, forUp, Stmt.NoRand]

/-- Initializing the identity fresh-name tables takes at most `20 * m + 7` steps,
writes only `[forward, forward + m)` and `[inverse, inverse + m)`, and preserves
all registers other than scratch register `0`. -/
theorem initFreshIdentityTables_runs {w m forward inverse : ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h81 : st.regs 81 = forward) (h82 : st.regs 82 = inverse) (h84 : st.regs 84 = m)
    (hdisj : forward + m ≤ inverse) (hroom : inverse + m < 2 ^ w) (hw1 : 1 < 2 ^ w) :
    ∃ out cost, Runs w p ω initFreshIdentityTables st .normal out cost ∧
      (∀ e < m, out.mem (forward + e) = e) ∧
      (∀ e < m, out.mem (inverse + e) = e) ∧
      (∀ a, (a < forward ∨ forward + m ≤ a) → (a < inverse ∨ inverse + m ≤ a) →
        out.mem a = st.mem a) ∧
      (∀ r ≠ 0, out.regs r = st.regs r) ∧
      out.pos = st.pos ∧ cost ≤ 20 * m + 7 := by
  let Inv (i : ℕ) (s : State) : Prop :=
    s.regs 0 = i ∧ s.pos = st.pos ∧
    (∀ r ≠ 0, s.regs r = st.regs r) ∧
    (∀ e < i, s.mem (forward + e) = e) ∧
    (∀ e < i, s.mem (inverse + e) = e) ∧
    (∀ a, (a < forward ∨ forward + i ≤ a) → (a < inverse ∨ inverse + i ≤ a) →
      s.mem a = st.mem a)
  have hmW : m < 2 ^ w := by omega
  have hloop := Triple.forRange_le (w := w) (p := p) (r := 0) (lo := .const 0) (hi := .reg 84)
    (P := fun s => s = st) (Inv := Inv) (fun _ => 11) 0 m (Nat.zero_le m) hw1 (fun _ => hmW)
    (fun s hs => by
      subst hs
      refine ⟨by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl,
        fun r hr => by simp [Function.update_of_ne hr],
        fun _ h => absurd h (Nat.not_lt_zero _),
        fun _ h => absurd h (Nat.not_lt_zero _), fun _ _ _ => rfl⟩)
    (fun _ _ _ _ hs => hs.1)
    (fun _ s _ _ hs => by simp [Expr.eval, hs.2.2.1 84 (by decide), h84])
    (fun i _ hi => by
      intro s ω' hs
      obtain ⟨h0, hpos, hregs, hf, hinv, hframe⟩ := hs
      have h81s : s.regs 81 = forward := (hregs 81 (by decide)).trans h81
      have h82s : s.regs 82 = inverse := (hregs 82 (by decide)).trans h82
      have hiF : forward + i < 2 ^ w := by omega
      have hiI : inverse + i < 2 ^ w := by omega
      let s1 := { s with mem := Function.update s.mem (forward + i) i }
      let s2 := { s1 with mem := Function.update s1.mem (inverse + i) i }
      have hr1 : Runs w p ω' (.store (.bin .add (.reg 81) (.reg 0)) (.reg 0)) s .normal s1 5 :=
        runs_store_iff.mpr ⟨forward + i, i,
          by simp [Expr.eval, BinOp.eval, h81s, h0, hiF],
          by simp [Expr.eval, h0], rfl, rfl, rfl⟩
      have hr2 : Runs w p ω' (.store (.bin .add (.reg 82) (.reg 0)) (.reg 0)) s1 .normal s2 5 :=
        runs_store_iff.mpr ⟨inverse + i, i,
          by simp [Expr.eval, BinOp.eval, s1, h82s, h0, hiI],
          by simp [Expr.eval, s1, h0], rfl, rfl, rfl⟩
      have hrun : Runs w p ω'
          (.store (.bin .add (.reg 81) (.reg 0)) (.reg 0) ;;
           .store (.bin .add (.reg 82) (.reg 0)) (.reg 0)) s .normal s2 11 :=
        runs_seq_iff.mpr (Or.inr ⟨s1, 5, 5, hr1, hr2, rfl⟩)
      refine ⟨.normal, s2, 11, hrun, ⟨⟨by simp, hpos, fun r hr => by simp [s2, s1, Function.update_of_ne hr, hregs r hr], ?_, ?_, ?_⟩, h0⟩, le_rfl⟩
      · intro e he
        by_cases h : e = i
        · subst h
          simp [s2, s1, Function.update_of_ne (show forward + e ≠ inverse + e by omega)]
        · have he' : e < i := by omega
          simp only [s2, s1]
          rw [Function.update_of_ne (show forward + e ≠ inverse + i by omega),
            Function.update_of_ne (show forward + e ≠ forward + i by omega)]
          exact hf e he'
      · intro e he
        by_cases h : e = i
        · subst h; simp [s2]
        · have he' : e < i := by omega
          simp only [s2, s1]
          rw [Function.update_of_ne (show inverse + e ≠ inverse + i by omega),
            Function.update_of_ne (show inverse + e ≠ forward + i by omega)]
          exact hinv e he'
      · intro a hfa hia
        simp only [s2, s1]
        rw [Function.update_of_ne (show a ≠ inverse + i by omega),
          Function.update_of_ne (show a ≠ forward + i by omega)]
        exact hframe a (by omega) (by omega))
  obtain ⟨o, out, c, hrun, hout, hcost⟩ := hloop.runs ω rfl
  cases o with
  | returned _ => exact False.elim hout
  | normal =>
    have hrc : rangeCost (fun _ => 11) 0 m = 11 * m := by
      simp [rangeCost, Nat.mul_comm]
    simp only [Expr.size, hrc] at hcost
    exact ⟨out, c, hrun, hout.2.2.2.1, hout.2.2.2.2.1, hout.2.2.2.2.2,
      hout.2.2.1, hout.2.1, by omega⟩

/-- Post-levels Init body: loads `m` and `n`, reserves the zeroed Algorithm 2
schedule and counter arrays, initializes the identity fresh-name tables and
counter, initializes the Section 6 path tree, and installs the Detect header
descriptors at `[handle, handle + 5)`. Leaves the new free heap in register `99`. -/
@[expose] def finishSolverInitBody (treeInit : ℕ) : Stmt :=
  .assign 84 (.load (.bin .add (.reg 74) (.const 9))) ;;
  .assign 92 (.load (.bin .add (.reg 69) (.const 2))) ;;
  .assign 85 (.bin .add (.reg 4)
    (.bin .add (.bin .mul (.const 4) (.bin .add (.reg 75) (.const 1))) (.const 1))) ;;
  .store (.reg 85) (.reg 84) ;;
  .assign 81 (.bin .add (.reg 85) (.const 1)) ;;
  .assign 82 (.bin .add (.reg 81) (.reg 84)) ;;
  .assign 83 (.bin .add (.reg 82) (.reg 84)) ;;
  .assign 99 (.bin .add (.reg 83) (.reg 84)) ;;
  initFreshIdentityTables ;;
  initPathTreeAtHeap treeInit 92 ;;
  storeMinRatioDetectDescriptors

theorem finishSolverInitBody_noRand (treeInit : ℕ) :
    (finishSolverInitBody treeInit).NoRand := by
  simp [finishSolverInitBody, initFreshIdentityTables_noRand, initPathTreeAtHeap,
    callInitPathTree, storeMinRatioDetectDescriptors, Stmt.NoRand]

/-- Execution of `finishSolverInitBody`: installs the Algorithm 2 schedule
block, fresh-name tables, Section 6 path tree, and Detect descriptors while
preserving the chain header, numeric header, threshold table, rebuilt levels,
and caller memory. -/
theorem finishSolverInitBody_runs
    {w handle rootGraph d m n L P searchSpace readSpace levelsEnd treeInit treeConst : ℕ}
    {fmt : Num.Format w} {treeAlloc : ℕ → ℕ → List ℕ → ℕ}
    {Rtree : DSRep PathTreeState} {treeOp : ℕ → ℕ}
    {p : Program} {ω : ℕ → Bool} {st : State}
    (h74 : st.regs 74 = handle) (h75 : st.regs 75 = d)
    (h69 : st.regs 69 = rootGraph) (h67 : st.regs 67 = L)
    (h4 : st.regs 4 = levelsEnd)
    (hmCell : st.mem (handle + 9) = m) (hnCell : st.mem (rootGraph + 2) = n)
    (hnum : MinRatioNumericHeaderAt st.mem handle L P searchSpace readSpace)
    (hz : ZeroFrom st.mem levelsEnd)
    (hhandleBelow : handle + 16 < levelsEnd)
    (hrootBelow : rootGraph + 2 < levelsEnd)
    (htreeImpl : Rtree.Implements w p treeInit treeOp
      (pathTreeMachineContract fmt L treeConst treeAlloc))
    (hLWord : L < 2 ^ w) (hPWord : fmt.precision < 2 ^ w)
    (hnWord : 2 * n + 1 < 2 ^ w) (hnFit : Nat.log 2 (2 * n + 1) ≤ fmt.limbBits * L)
    (hroom :
      let freshCounter := levelsEnd + (4 * (d + 1) + 1)
      let treeHeap := freshCounter + 1 + m + m + m
      treeHeap + treeAlloc 7 n [n, L, treeHeap] < 2 ^ w)
    (hw16 : 16 < 2 ^ w) :
    let freshCounter := levelsEnd + (4 * (d + 1) + 1)
    let forward := freshCounter + 1
    let inverse := forward + m
    let thresholds := inverse + m
    let treeHeap := thresholds + m
    ∃ out cost sTree xTree finalHeap,
      Runs w p ω (finishSolverInitBody treeInit) st .normal out cost ∧
      out.regs 74 = handle ∧ out.regs 80 = treeHeap ∧ out.regs 81 = forward ∧
      out.regs 82 = inverse ∧ out.regs 83 = thresholds ∧ out.regs 84 = m ∧
      out.regs 85 = freshCounter ∧ out.regs 99 = finalHeap ∧
      DetectHeaderAt out.mem handle treeHeap forward inverse thresholds m L searchSpace readSpace ∧
      MinRatioNumericHeaderAt out.mem handle L P searchSpace readSpace ∧
      (∀ a, levelsEnd ≤ a → a < freshCounter → out.mem a = 0) ∧
      FreshTablesAt out.mem forward inverse freshCounter m m id id m ∧
      Rtree.rep treeHeap sTree xTree out.mem ∧
      (pathTreeMachineContract fmt L treeConst treeAlloc).initPost [n, L, treeHeap]
        out.mem sTree out.mem ∧
      ZeroFrom out.mem finalHeap ∧ treeHeap ≤ finalHeap ∧
      finalHeap ≤ treeHeap + treeAlloc 7 n [n, L, treeHeap] ∧
      (∀ a, Rtree.foot treeHeap xTree a → treeHeap ≤ a ∧ a < finalHeap) ∧
      (∀ a < levelsEnd, (a < handle ∨ handle + 4 < a) → out.mem a = st.mem a) ∧
      cost + Rtree.phi treeHeap xTree out.mem ≤
        treeConst * (L + 1) ^ 2 * (n + 1) + 20 * m + 92 := by
  dsimp only
  let freshCounter := levelsEnd + (4 * (d + 1) + 1)
  let forward := freshCounter + 1
  let inverse := forward + m
  let thresholds := inverse + m
  let treeHeap := thresholds + m
  have hw4 : 4 < 2 ^ w := lt_trans (by decide : 4 < 16) hw16
  have hw9 : 9 < 2 ^ w := lt_trans (by decide : 9 < 16) hw16
  have hw1 : 1 < 2 ^ w := lt_trans (by decide : 1 < 16) hw16
  have htreeW : treeHeap < 2 ^ w := by omega
  let s1 := { st with regs := Function.update st.regs 84 m }
  let s2 := { s1 with regs := Function.update s1.regs 92 n }
  let s3 := { s2 with regs := Function.update s2.regs 85 freshCounter }
  let s4 := { s3 with mem := Function.update s3.mem freshCounter m }
  let s5 := { s4 with regs := Function.update s4.regs 81 forward }
  let s6 := { s5 with regs := Function.update s5.regs 82 inverse }
  let s7 := { s6 with regs := Function.update s6.regs 83 thresholds }
  let s8 := { s7 with regs := Function.update s7.regs 99 treeHeap }
  have hr1 : Runs w p ω (.assign 84 (.load (.bin .add (.reg 74) (.const 9)))) st .normal s1 5 :=
    runs_assign_iff.mpr ⟨m, by
      simp [Expr.eval, BinOp.eval, h74, hmCell, hw9, show handle + 9 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hr2 : Runs w p ω (.assign 92 (.load (.bin .add (.reg 69) (.const 2)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨n, by
      simp [Expr.eval, BinOp.eval, s1, h69, hnCell, show 2 < 2 ^ w by omega,
        show rootGraph + 2 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hr3 : Runs w p ω (.assign 85 (.bin .add (.reg 4)
      (.bin .add (.bin .mul (.const 4) (.bin .add (.reg 75) (.const 1))) (.const 1))))
      s2 .normal s3 10 :=
    runs_assign_iff.mpr ⟨freshCounter, by
      simp [Expr.eval, BinOp.eval, s2, s1, h4, h75, freshCounter, hw4, hw1,
        show d + 1 < 2 ^ w by omega, show 4 * (d + 1) < 2 ^ w by omega,
        show 4 * (d + 1) + 1 < 2 ^ w by omega, show levelsEnd + (4 * (d + 1) + 1) < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hr4 : Runs w p ω (.store (.reg 85) (.reg 84)) s3 .normal s4 3 :=
    runs_store_iff.mpr ⟨freshCounter, m, by simp [Expr.eval, s3],
      by simp [Expr.eval, s3, s2, s1], rfl, rfl, rfl⟩
  have hr5 : Runs w p ω (.assign 81 (.bin .add (.reg 85) (.const 1))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨forward, by
      simp [Expr.eval, BinOp.eval, s4, s3, forward, hw1, show freshCounter + 1 < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hr6 : Runs w p ω (.assign 82 (.bin .add (.reg 81) (.reg 84))) s5 .normal s6 4 :=
    runs_assign_iff.mpr ⟨inverse, by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, inverse, show forward + m < 2 ^ w by omega],
      rfl, rfl, rfl⟩
  have hr7 : Runs w p ω (.assign 83 (.bin .add (.reg 82) (.reg 84))) s6 .normal s7 4 :=
    runs_assign_iff.mpr ⟨thresholds, by
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, thresholds,
        show inverse + m < 2 ^ w by omega], rfl, rfl, rfl⟩
  have hr8 : Runs w p ω (.assign 99 (.bin .add (.reg 83) (.reg 84))) s7 .normal s8 4 :=
    runs_assign_iff.mpr ⟨treeHeap, by
      simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, treeHeap, htreeW],
      rfl, rfl, rfl⟩
  obtain ⟨s9, freshCost, hrFresh, hfwd9, hinv9, hframe9, hregs9, _, hfreshCost⟩ :=
    initFreshIdentityTables_runs (w := w) (m := m) (forward := forward) (inverse := inverse)
      (p := p) (ω := ω) (st := s8)
      (by simp [s8, s7, s6, s5]) (by simp [s8, s7, s6]) (by simp [s8, s7, s6, s5, s4, s3, s2, s1])
      le_rfl (by omega) hw1
  have hz9 : ZeroFrom s9.mem treeHeap := by
    intro a ha
    rw [hframe9 a (Or.inr (by omega)) (Or.inr (by omega))]
    simp only [s8, s7, s6, s5, s4, s3, s2, s1]
    rw [Function.update_of_ne (show a ≠ freshCounter by omega)]
    exact hz a (by omega)
  have htreePre := pathTree_initPre_of_runtimeFormat (fmt := fmt) (L := L)
    (constant := treeConst) (allocation := treeAlloc) (mem := s9.mem)
    (n := n) (heap := treeHeap) hnWord hLWord hPWord hnFit
  obtain ⟨s10, treeCost, sTree, xTree, finalHeap, hrTree, h80_10, h99_10, hkeep10,
      hrep10, hpost10, hresp10, htreeCost⟩ :=
    initPathTreeAtHeap_runs (ω := ω) (st := s9) htreeImpl (by decide : 92 ≠ 80)
      ((hregs9 92 (by decide)).trans (by simp [s8, s7, s6, s5, s4, s3, s2]))
      ((hregs9 67 (by decide)).trans (by simp [s8, s7, s6, s5, s4, s3, s2, s1, h67]))
      ((hregs9 99 (by decide)).trans (by simp [s8]))
      (by
        intro a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
        rcases ha with rfl | rfl | rfl <;> omega)
      htreePre hz9 hroom
  have hkeepBelow10 (a : ℕ) (ha : a < treeHeap) : s10.mem a = s9.mem a :=
    hresp10.2.2.2.1 a ha (by simp)
  have hnum10 : MinRatioNumericHeaderAt s10.mem handle L P searchSpace readSpace := by
    intro j hj
    have hj4 : j < 4 := by simpa [List.length] using hj
    have hlt : handle + 5 + j < levelsEnd := by omega
    rw [hkeepBelow10 _ (by omega), hframe9 _ (Or.inl (by omega)) (Or.inl (by omega))]
    simp only [s8, s7, s6, s5, s4, s3, s2, s1]
    rw [Function.update_of_ne (show handle + 5 + j ≠ freshCounter by omega)]
    exact hnum j hj
  have hreg10 (r : ℕ) (h0 : r ≠ 0) (h80 : r ≠ 80) (h99 : r ≠ 99) : s10.regs r = s8.regs r :=
    (hkeep10 r h80 h99).trans (hregs9 r h0)
  obtain ⟨out, hrDesc, hdetect, hnumOut, hframeDesc, hregsDesc, _⟩ :=
    storeMinRatioDetectDescriptors_runs (w := w) (p := p) (ω := ω) (st := s10)
      (handle := handle) (tree := treeHeap) (names := forward) (inverse := inverse)
      (thresholds := thresholds) (count := m)
      ((hreg10 74 (by decide) (by decide) (by decide)).trans (by simp [s8, s7, s6, s5, s4, s3, s2, s1, h74]))
      h80_10
      ((hreg10 81 (by decide) (by decide) (by decide)).trans (by simp [s8, s7, s6, s5]))
      ((hreg10 82 (by decide) (by decide) (by decide)).trans (by simp [s8, s7, s6]))
      ((hreg10 83 (by decide) (by decide) (by decide)).trans (by simp [s8, s7]))
      ((hreg10 84 (by decide) (by decide) (by decide)).trans (by simp [s8, s7, s6, s5, s4, s3, s2, s1]))
      hnum10 (by omega)
  have hfoot10 (a : ℕ) (ha : Rtree.foot treeHeap xTree a) : treeHeap ≤ a ∧ a < finalHeap :=
    (hresp10.2.2.2.2 a ha).resolve_left id
  have htreeAgree : ∀ a, Rtree.foot treeHeap xTree a → s10.mem a = out.mem a := by
    intro a ha
    have hlo := (hfoot10 a ha).1
    exact (hframeDesc a (Or.inr (by omega))).symm
  have hrepOut : Rtree.rep treeHeap sTree xTree out.mem :=
    (htreeImpl.1 treeHeap sTree xTree s10.mem out.mem htreeAgree).1 hrep10
  have hphiOut : Rtree.phi treeHeap xTree out.mem = Rtree.phi treeHeap xTree s10.mem :=
    (htreeImpl.1 treeHeap sTree xTree s10.mem out.mem htreeAgree).2.symm
  let tailCost := freshCost + (treeCost + 29 + 1) + 1
  have hrunTotal : Runs w p ω (finishSolverInitBody treeInit) st .normal out (47 + tailCost) := by
    unfold finishSolverInitBody
    have ht1 : Runs w p ω (initPathTreeAtHeap treeInit 92 ;; storeMinRatioDetectDescriptors)
        s9 .normal out (treeCost + 29 + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s10, treeCost, 29, hrTree, hrDesc, rfl⟩)
    have ht2 : Runs w p ω (initFreshIdentityTables ;; initPathTreeAtHeap treeInit 92 ;;
        storeMinRatioDetectDescriptors) s8 .normal out tailCost :=
      runs_seq_iff.mpr (Or.inr ⟨s9, freshCost, treeCost + 29 + 1, hrFresh, ht1, rfl⟩)
    have ht3 := runs_seq_iff.mpr (Or.inr ⟨s8, 4, tailCost, hr8, ht2, rfl⟩)
    have ht4 := runs_seq_iff.mpr (Or.inr ⟨s7, 4, 4 + tailCost + 1, hr7, ht3, rfl⟩)
    have ht5 := runs_seq_iff.mpr (Or.inr ⟨s6, 4, 4 + (4 + tailCost + 1) + 1, hr6, ht4, rfl⟩)
    have ht6 := runs_seq_iff.mpr (Or.inr ⟨s5, 4, 4 + (4 + (4 + tailCost + 1) + 1) + 1, hr5, ht5, rfl⟩)
    have ht7 := runs_seq_iff.mpr (Or.inr ⟨s4, 3, _, hr4, ht6, rfl⟩)
    have ht8 := runs_seq_iff.mpr (Or.inr ⟨s3, 10, _, hr3, ht7, rfl⟩)
    have ht9 := runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, hr2, ht8, rfl⟩)
    exact runs_seq_iff.mpr (Or.inr ⟨s1, 5, _, hr1, ht9, by omega⟩)
  refine ⟨out, 47 + tailCost, sTree, xTree, finalHeap,
    hrunTotal,
    by rw [hregsDesc, hreg10 74 (by decide) (by decide) (by decide)]; simp [s8, s7, s6, s5, s4, s3, s2, s1, h74],
    by rw [hregsDesc]; exact h80_10,
    by rw [hregsDesc, hreg10 81 (by decide) (by decide) (by decide)]; simp [s8, s7, s6, s5]; rfl,
    by rw [hregsDesc, hreg10 82 (by decide) (by decide) (by decide)]; simp [s8, s7, s6]; rfl,
    by rw [hregsDesc, hreg10 83 (by decide) (by decide) (by decide)]; simp [s8, s7]; rfl,
    by rw [hregsDesc, hreg10 84 (by decide) (by decide) (by decide)]; simp [s8, s7, s6, s5, s4, s3, s2, s1],
    by rw [hregsDesc, hreg10 85 (by decide) (by decide) (by decide)]; simp [s8, s7, s6, s5, s4, s3]; rfl,
    by rw [hregsDesc]; exact h99_10,
    hdetect, hnumOut, ?_, ?_, hrepOut, ?_, ?_, hresp10.1, hresp10.2.1, hfoot10, ?_, ?_⟩
  · intro a hlo hhi
    rw [hframeDesc a (Or.inr (by omega)), hkeepBelow10 a (by omega),
      hframe9 a (Or.inl (by omega)) (Or.inl (by omega))]
    simp only [s8, s7, s6, s5, s4, s3, s2, s1]
    rw [Function.update_of_ne (show a ≠ freshCounter by omega)]
    exact hz a hlo
  · refine ⟨?_, ?_, ?_⟩
    · rw [hframeDesc _ (Or.inr (by omega)), hkeepBelow10 _ (by omega),
        hframe9 _ (Or.inl (by omega)) (Or.inl (by omega))]
      change s8.mem freshCounter = m
      simp [s8, s7, s6, s5, s4]
    · intro e he
      rw [hframeDesc _ (Or.inr (by omega)), hkeepBelow10 _ (by omega)]
      exact hfwd9 e he
    · intro e he
      rw [hframeDesc _ (Or.inr (by omega)), hkeepBelow10 _ (by omega)]
      exact hinv9 e he
  · exact hpost10
  · intro a ha
    have hlo := hresp10.1
    exact (hframeDesc a (Or.inr (by omega))).trans (hresp10.2.2.1 a ha)
  · intro a ha hdisj
    rw [hframeDesc a hdisj, hkeepBelow10 a (by omega),
      hframe9 a (Or.inl (by omega)) (Or.inl (by omega))]
    simp only [s8, s7, s6, s5, s4, s3, s2, s1]
    rw [Function.update_of_ne (show a ≠ freshCounter by omega)]
  · rw [hphiOut]
    omega

private theorem tail_vec_lt_heap {base e L m heap j : ℕ}
    (he : e < m) (hj : j < L) (hend : base + m * L ≤ heap) :
    base + e * L + j < heap := by
  have hm : (e + 1) * L ≤ m * L := Nat.mul_le_mul_right L (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at hm
  omega

private theorem tail_le_heap_to_le_levelTable {u heap L g table d : ℕ}
    (hu : u ≤ heap) (ht : heap + (L + 1) + 6 + g ≤ table) :
    u ≤ table + (d + 1) + 17 := by omega

private theorem tail_handle_chain_lt_levelTable {table d j : ℕ} (hj : j < 8) :
    table + (d + 1) + 9 + j < table + (d + 1) + 17 := by omega

private theorem tail_handle_num_lt_levelTable {table d j : ℕ} (hj : j < 4) :
    table + (d + 1) + 5 + j < table + (d + 1) + 17 := by omega

private theorem tail_root_n_lt_levelTable {heap L g table d : ℕ}
    (hg3 : 3 ≤ g) (ht : heap + (L + 1) + 6 + g ≤ table) :
    heap + (L + 1) + 6 + 2 < table + (d + 1) + 17 := by omega

private theorem tail_handle_end_lt_lev {table d lev : ℕ}
    (h : table + (d + 1) + 17 + (d + 1) + (d + 1) ≤ lev) :
    table + (d + 1) + 16 < lev := by omega

private theorem tail_root_n_lt_lev {heap L g table d lev : ℕ}
    (hg3 : 3 ≤ g) (ht : heap + (L + 1) + 6 + g ≤ table)
    (h : table + (d + 1) + 17 + (d + 1) + (d + 1) ≤ lev) :
    heap + (L + 1) + 6 + 2 < lev := by omega

private theorem tail_lev_le_treeHeap (lev d m : ℕ) :
    lev ≤ lev + (4 * (d + 1) + 1) + 1 + m + m + m := by omega

private theorem tail_heap_le_final {heap L g table d lev final : ℕ}
    (ht : heap + (L + 1) + 6 + g ≤ table)
    (h : table + (d + 1) + 17 + (d + 1) + (d + 1) ≤ lev) (hf : lev ≤ final) :
    heap ≤ final := by omega

private theorem tail_x_lt_lev {x heap L g table d lev : ℕ}
    (hx : x < heap) (ht : heap + (L + 1) + 6 + g ≤ table)
    (h : table + (d + 1) + 17 + (d + 1) + (d + 1) ≤ lev) :
    x < lev ∧ x < table + (d + 1) ∧ x < table + (d + 1) + 17 := by omega

private theorem tail_chain_in_lev {table d lev j : ℕ} (hj : j < 8)
    (h : table + (d + 1) + 17 + (d + 1) + (d + 1) ≤ lev) :
    table + (d + 1) + 9 + j < lev ∧ table + (d + 1) + 4 < table + (d + 1) + 9 + j := by omega

private theorem tail_table_in_lev {table d lev j : ℕ} (hj : j ≤ d)
    (h : table + (d + 1) + 17 + (d + 1) + (d + 1) ≤ lev) :
    table + j < lev ∧ table + j < table + (d + 1) ∧ table + j < table + (d + 1) + 17 := by omega

private theorem tail_core_cell_in_lev {table d lev j : ℕ} (hj : j ≤ d)
    (h : table + (d + 1) + 17 + (d + 1) + (d + 1) ≤ lev) :
    table + (d + 1) + 17 + j < lev ∧
    table + (d + 1) + 4 < table + (d + 1) + 17 + j ∧
    table + (d + 1) + 17 + (d + 1) + j < lev ∧
    table + (d + 1) + 4 < table + (d + 1) + 17 + (d + 1) + j := by omega

private theorem tail_foot_above_desc {table d x a : ℕ}
    (hx : table + (d + 1) + 17 + d < x) (ha : x ≤ a) :
    table + (d + 1) + 4 < a := by omega

private theorem tail_term_foot_above_desc {table d a : ℕ}
    (ha : table + (d + 1) + 17 + (d + 1) + (d + 1) ≤ a) :
    table + (d + 1) + 4 < a := by omega

/-- Complete fixed deterministic Init program returning the new free heap
pointer in register `99`, matching the `WordRAM.DSRep.Implements` convention. -/
@[expose] def solverInitCompleteProgram
    (alpha select quality graphPack threshold b clog lsstConstant
      factorEntry decK thr cDeg witnessDen coefficient power extend mul shift add
      init read forestOp copy sort entry terminalInit treeInit : ℕ)
    (retry degreeSetup inconclusive : Stmt) : Stmt :=
  solverInitFullProgram alpha select quality graphPack threshold b clog lsstConstant
    factorEntry decK thr cDeg witnessDen coefficient power extend mul shift add
    retry degreeSetup
    (buildSolverInitLevels init read forestOp copy sort entry terminalInit ;;
      finishSolverInitBody treeInit)
    inconclusive ;;
  .ret (.reg 99)

/-- End-to-end complete Init run for `sparseCoreRestartTool`,
`fixedPointLastLevelTool`, and the Section 6 path tree: from the seven-word
IPM entry `[graph, gradient, lengths, L, P, V, heap]`, under one uniform
`wordSize` multiplier, builds all `C.d` sparse cores and the terminal level,
reserves the zeroed Algorithm 2 schedule arrays, initializes the identity
fresh-name tables (`nextFresh = I.m`), initializes the Section 6 path tree,
installs the Detect and chain headers, preserves caller memory `< heap`, and
returns the fresh heap pointer `finalHeap`. -/
theorem solverInitCompleteProgram_fixedPoint_runs
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (scDepth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (alpha select quality graphPack threshold b clog lsstConstant
      Kγ pathC Kint cw factorEntry decK thr cDeg witnessDen coefficient
      power extend mul shift add init copy sort entry terminalInit treeInit treeConst q dh : ℕ)
    (op lastOp treeOp : ℕ → ℕ)
    (hK : 1 ≤ decK) (hcDeg : 0 < cDeg) (hWitness : 0 < witnessDen) :
    ∃ multiplier, ∀ (J : Scaling.Circulation) (E : SparseCore.SparseCoreEnv)
      {R : DSRep (sparseCoreRestartTool oracle C_lsst scDepth sparsify).State}
      {terminal : DSRep (ℕ × (ℕ → LSF))}
      {Rtree : DSRep PathTreeState}
      {costs : SparseCoreMachineCosts}
      {allocation : ℕ → ℕ → List ℕ → ℕ} {lastAllocation : ℕ → List ℕ → ℕ}
      {treeAlloc : ℕ → ℕ → List ℕ → ℕ}
      {lastMult stretchPrecision : ℕ}
      {Mcap Ncap scanExponent nextGraphSizeCap : ℕ → ℕ} {gradientBound : ℕ → ℝ}
      {c graph gradient lengths heap pos : ℕ}
      {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
      {qualityExponent qualityCharge : ℕ → ℕ}
      {retry degreeSetup inconclusive : Stmt},
      let B := J.solverWords.length + J.solverWords.foldr max 0 + 2
      let w := wordSize c J.solverWords
      let I := IPM.Machine.solverConnectedAugmented J
      let V := IPM.Machine.solverPenalty J.m
      let G := IPM.namedInstance I
      let k := qualityExponent G.m
      let L := IPM.Machine.ipmQualityLimbs I.m V k
      let P := IPM.Machine.ipmQualityPrecision I.m V k
      let M := max I.m threshold
      let T := sparseCoreRestartTool oracle C_lsst scDepth sparsify
      let lastTool := LastLevelProgram.fixedPointLastLevelTool oracle C_lsst
      let len₀ := IPM.Machine.readVector mem lengths 4 L P I.m
      let grad₀ := IPM.Machine.readVector mem gradient 4 L P I.m
      J.n ≤ 2 * J.m + 1 → 0 < J.m → (∀ e, 1 ≤ J.capacity e) → I.IsValid →
      2 ^ k ≤ (J.n + J.m + 2) ^ q →
      heap ≤ B ^ dh →
      ∀ (hqw : IPM.Machine.ipmQualityParameterWordBits I.m V k ≤ w),
      multiplier ≤ c →
      ∀ (hM : 1 ≤ M),
      let fmt := (IPM.Machine.ipmQualityMinRatioFormat I.m V k hqw).fmt
      let C := Chain.concreteChainParams M hM
      let chain := (algorithm1_initialize T lastTool C Mcap (Ncap 0) G len₀ grad₀).1
      let Ψ := IPM.Machine.ipmQualityRangeExponent I.m V k + IPM.Machine.slackRangeExponent I.m V + 6
      let den := Expander.maxPhiDenOf decK thr (M ^ 2)
      let cap := Spanner.capM_W cDeg (1 / (den : ℝ)) (M ^ 2)
      let growth := (max (Expander.PathDSProg.gExpImpl Kγ pathC Kint den (M ^ 2))
        (Expander.PathDSProg.gExpImpl Kγ pathC Kint witnessDen cap)) ^ 2
      let epsExp := Num.IPM.alphaExponent I.m V + k + 10
      MeetsContract w p quality (IPM.Machine.solverQualityContract w qualityExponent qualityCharge) →
      MeetsContract w p alpha (Num.IPM.alphaContract w 4) →
      MeetsContract w p select (IPM.Machine.precisionSelectionContract w) →
      MeetsContract w p graphPack
        (dgInitFromListsContract w G.n G.m G (G.V.sort (· ≤ ·))
          ((G.E.sort (· ≤ ·)).map (fun e => (e, G.tail e, G.head e)))) →
      p.HasAt b (initDepthProcedures b 4) →
      p.HasAt clog (Scaling.Machine.clogTwoModule clog) →
      MeetsContract w p factorEntry (initMachinePathFactorsContract w Kγ pathC Kint cw) →
      MeetsContract w p power (initStretchPowerContract w) →
      MeetsContract w p extend (Num.extendCopyContract w 4) →
      MeetsContract w p mul (Num.multiplyContract w 4) →
      MeetsContract w p shift (Num.shiftLeftContract w 4) →
      MeetsContract w p add (Num.addContract w 4) →
      MeetsContract w p copy (copyWordsContract w) →
      MeetsContract w p sort (Expander.heapSortContract w) →
      (∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w 4 x y z)) →
      Rtree.Implements w p treeInit treeOp (pathTreeMachineContract fmt L treeConst treeAlloc) →
      IPM.Machine.GraphAt mem graph G →
      graph + (IPM.Machine.graphWords G).length ≤ heap →
      lengths + G.m * L ≤ heap →
      gradient + G.m * L ≤ heap →
      (∀ e < I.m, Num.Valid mem (lengths + e * L) 4 L ∧ Num.Valid mem (gradient + e * L) 4 L) →
      ZeroFrom mem heap →
      E.L = Expander.chosenL (M ^ 2) →
      (E.P_fn (M ^ 2)).γ_ℓ = growth →
      1 ≤ (E.P_fn (M ^ 2)).K_s →
      (E.P_fn (M ^ 2)).p_s = 1 →
      (E.P_fn (M ^ 2)).K_s = 1 + coefficient / Real.log 2 →
      (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ M →
      (SparseCore.sparseCoreParams E).γ_ℓ (M ^ 2) ≤ C.k →
      E.B_fn (M ^ 2) = Chain.concreteBucketCap lsstConstant Ψ C.k C.d (4 * M) →
      (∀ factors,
        factors.regs 22 = M → factors.regs 44 = E.L → factors.regs 47 = E.B_fn (M ^ 2) →
        factors.regs 50 = growth → factors.regs 4 = 1 →
        ∃ capped degCost,
          Runs w p ω degreeSetup factors .normal capped degCost ∧
          capped.regs 48 = E.d_fn (M ^ 2) ∧ capped.mem = factors.mem ∧
          ∀ r ≠ 48, capped.regs r = factors.regs r) →
      R.Local → terminal.Local → C.d < 2 ^ w → C.k < 2 ^ w →
      2 * G.n + 1 < 2 ^ w → Nat.log 2 (2 * G.n + 1) ≤ 4 * L →
      (∀ i, i < C.d → Ncap i = Ncap 0) →
      (chain.G C.d).IsValid →
      (∀ i, i < C.d → ∀ vc ec,
        R.Implements w p init op
          (sparseCoreMachineContract fmt L T (chain.G i) C.k (Mcap i) (Ncap i) vc ec costs (allocation i))) →
      (∀ vc ec,
        terminal.Implements w p terminalInit lastOp
          (lastLevelRuntimeMachineContract fmt L lastTool (chain.G C.d) vc ec
            lastMult stretchPrecision lastAllocation)) →
      (∀ i, i < C.d →
        let Gi := chain.G i
        let Hi := chain.G (i + 1)
        let leni := chain.toTreeChain.chainLen len₀ i
        let gradi := chain.toTreeChain.chainGrad grad₀ i
        let forest := T.lsfs (chain.scState i) 0
        Gi.m ≤ Mcap i ∧ Gi.n ≤ Ncap i ∧ (∀ e ∈ Gi.E, 0 < leni e) ∧
        forest.T.IsForest ∧ forest.T.E ⊆ Gi.E ∧ Gi.V ⊆ forest.T.V ∧ Hi.E ⊆ Gi.E ∧
        2 * forest.T.n + 2 < 2 ^ w ∧
        P + scanExponent i + 2 ≤ 4 * L ∧
        0 ≤ gradientBound i ∧ (∀ e ∈ Gi.E, |gradi e| ≤ gradientBound i) ∧
        (2 * (forest.T.m : ℝ) + 1) * gradientBound i ≤ (2 : ℝ) ^ scanExponent i) →
      (∀ (ω' : ℕ → Bool) levelTable i, i < C.d → ∀ vc ec before,
        let Gi := chain.G i
        let Hi := chain.G (i + 1)
        let leni := chain.toTreeChain.chainLen len₀ i
        let forest := T.lsfs (chain.scState i) 0
        RebuildSuffixAt R chain len₀ grad₀ levelTable (levelTable + (C.d + 1)) 0 i vc ec
          4 L P before →
        InitLevelTablesSeparated levelTable C.d (before.regs 6) vc ec (before.regs 8) L →
        levelTable + (C.d + 1) + (C.d + 1) ≤ before.regs 4 →
        before.regs 4 + allocation i 5 [before.regs 6, before.regs 7, before.regs 8, before.regs 4] + 1 < 2 ^ w ∧
        ∀ args,
          Runs w p ω' prepareRebuildGraphArgs
            { before with regs := Function.update (Function.update before.regs 53 (before.regs 19)) 54 (before.regs 21) }
            .normal args 36 →
          (∀ mid top v e cost,
            Runs w p ω' (rebuildInstallReadGraph init (op 3)) args .normal mid cost →
            mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e Hi →
            mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) ∧
          (∀ mid c fv fe,
            Runs w p ω' (rebuildReadForest init (op 3) (op 2)) args .normal mid c →
            LSFAt mid.mem (mid.regs 9) fv fe 4 L P Gi.E forest →
            EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1)) 4 L P Gi.E leni) ∧
          (∀ s v e fv fe c,
            Runs w p ω' (rebuildReadForestLengths init (op 3) (op 2)) args .normal s c →
            DynGraphAt s.mem (s.regs 6) v e Hi →
            LSFAt s.mem (s.regs 9) fv fe 4 L P Gi.E forest →
            dynGraphSize v e ≤ nextGraphSizeCap (i + 1) ∧
            s.mem (s.regs 9) + dynGraphSize fv fe ≤ s.regs 5 ∧
            s.regs 7 + e * L ≤ s.regs 5 ∧ e ≤ ec ∧
            s.regs 5 + forest.T.n + 2 < 2 ^ w ∧
            s.regs 5 + forest.T.n + fv * L + L + fv + fv +
              3 * L * forest.T.vol forest.T.V + ec * L + 3 * L * Hi.m < 2 ^ w)) →
      (∀ e ∈ (chain.G C.d).E, 2 * (2 : ℝ) ^ stretchPrecision *
        lastLevelStretchBound (chain.G C.d) (chain.toTreeChain.chainLen len₀ C.d) e <
          Num.capacity 4 L) →
      (∀ e ∈ (chain.G C.d).E, 0 < chain.toTreeChain.chainLen len₀ C.d e) →
      (∀ levelTable vc ec before,
        RebuildSuffixAt R chain len₀ grad₀ levelTable (levelTable + (C.d + 1)) 0 C.d vc ec
          4 L P before →
        before.regs 4 + lastAllocation 1 [before.regs 6, before.regs 7, L, P, before.regs 4] < 2 ^ w) →
      (∀ (levelTable : ℕ) (afterLevels : State),
        RebuiltCoresAt R chain afterLevels.mem levelTable (levelTable + (C.d + 1)) 0 C.d (afterLevels.regs 4) →
        let treeHeap := afterLevels.regs 4 + (4 * (C.d + 1) + 1) + 1 + I.m + I.m + I.m
        treeHeap + treeAlloc 7 G.n [G.n, L, treeHeap] < 2 ^ w) →
      ∃ out cost table a levelsEnd finalHeap sTree xTree,
        let handle := table + (C.d + 1)
        let levelTable := handle + 17
        let freshCounter := levelsEnd + (4 * (C.d + 1) + 1)
        let forward := freshCounter + 1
        let inverse := forward + I.m
        let thresholds := inverse + I.m
        let treeHeap := thresholds + I.m
        Runs w p ω
          (solverInitCompleteProgram alpha select quality graphPack threshold b clog lsstConstant
            factorEntry decK thr cDeg witnessDen coefficient power extend mul shift add
            init (op 3) (op 2) copy sort entry terminalInit treeInit
            retry degreeSetup inconclusive)
          (startState [graph, gradient, lengths, L, P, V, heap] mem pos)
          (.returned finalHeap) out cost ∧
        DetectHeaderAt out.mem handle treeHeap forward inverse thresholds I.m L
          (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
        ChainInitParametersAt out.mem handle I.m V C.d C.k Ψ heap k epsExp ∧
        MinRatioNumericHeaderAt out.mem handle L P
          (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
        (∀ j ≤ C.d, out.mem (table + j) =
            Chain.concreteLevelRebuildCount M C.k a (concreteThresholdScale C.d) j (4 * M) ∧
          (out.mem (table + j) : ℝ) ≤
            Chain.SparseCoreTool.updateThreshold C.k
              (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ∧
          Chain.SparseCoreTool.updateThreshold C.k
              (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ≤
            48 * ((out.mem (table + j) : ℝ) + 1)) ∧
        RebuiltCoresAt R chain out.mem levelTable (levelTable + (C.d + 1)) 0 C.d finalHeap ∧
        out.mem (levelTable + (C.d + 1) + C.d) = chain.lastBran ∧
        (∃ y : terminal.τ, terminal.rep (out.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs)
          y out.mem ∧ ∀ addr, terminal.foot (out.mem (levelTable + C.d)) y addr → addr < finalHeap) ∧
        (∀ addr, levelsEnd ≤ addr → addr < freshCounter → out.mem addr = 0) ∧
        FreshTablesAt out.mem forward inverse freshCounter I.m I.m id id I.m ∧
        Rtree.rep treeHeap sTree xTree out.mem ∧
        ZeroFrom out.mem finalHeap ∧ heap ≤ finalHeap ∧
        (∀ x < heap, out.mem x = mem x) := by
  obtain ⟨mult, hprefix⟩ :=
    solverInitFullPrefix_runs alpha select quality graphPack threshold b clog lsstConstant
      Kγ pathC Kint cw factorEntry decK thr cDeg witnessDen coefficient
      power extend mul shift add q dh hK hcDeg hWitness
  refine ⟨mult, ?_⟩
  intro J E R terminal Rtree costs allocation lastAllocation treeAlloc lastMult stretchPrecision
    Mcap Ncap scanExponent nextGraphSizeCap gradientBound c graph gradient lengths heap pos
    p ω mem qualityExponent qualityCharge retry degreeSetup inconclusive
    B w I V G k L P M T lastTool len₀ grad₀
    hJn hJm hcap hIvalid hk hheapPow hqw hcmult hM fmt C chain Ψ den cap growth epsExp
    hqual halpha hselect hpack hdepthProc hclog hfactorImpl hpower hext hmul hshift hadd
    hcopy hsort hentry htreeImpl hGraph hGraphBelow hLenEnd hGradEnd hVecValid hz
    hEL hGrowth hK1 hps1 hCoeff hγM hγk hBfn hDegree hlocal htermLocal hdW hkW
    hnWord hnFit hNconst hValidLast hcoreImpl htermImpl hmodel hreadout hstretch hposLast hspaceLast htreeSpace
  have hfit := IPM.Machine.ipm_quality_parameter_words_fit I.m V k hqw
  have hw16 : 16 < 2 ^ w :=
    lt_of_lt_of_le (by decide : 16 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hfit.1)
  have hw9 : 9 < 2 ^ w := lt_trans (by decide : 9 < 16) hw16
  have hWidth4 : P ≤ 4 * L := by
    dsimp only [L, P, IPM.Machine.ipmQualityLimbs]
    omega
  have hGm : G.m = I.m := IPM.namedInstance_m I
  have hLenMem : EdgeValuesAt mem lengths 4 L P G.E len₀ := by
    intro e he
    have he' : e < I.m := Finset.mem_range.mp he
    refine ⟨(hVecValid e he').1, ?_⟩
    dsimp only [len₀, IPM.Machine.readVector]
    simp only [he', ↓reduceIte]
  have hGradMem : EdgeValuesAt mem gradient 4 L P G.E grad₀ := by
    intro e he
    have he' : e < I.m := Finset.mem_range.mp he
    refine ⟨(hVecValid e he').2, ?_⟩
    dsimp only [grad₀, IPM.Machine.readVector]
    simp only [he', ↓reduceIte]
  let Post (table a : ℕ) (out : State) : Prop :=
    ∃ levelsEnd finalHeap sTree xTree,
      let handle := table + (C.d + 1)
      let levelTable := handle + 17
      let freshCounter := levelsEnd + (4 * (C.d + 1) + 1)
      let forward := freshCounter + 1
      let inverse := forward + I.m
      let thresholds := inverse + I.m
      let treeHeap := thresholds + I.m
      out.regs 99 = finalHeap ∧
      DetectHeaderAt out.mem handle treeHeap forward inverse thresholds I.m L
        (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
      ChainInitParametersAt out.mem handle I.m V C.d C.k Ψ heap k epsExp ∧
      MinRatioNumericHeaderAt out.mem handle L P
        (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
      (∀ j ≤ C.d, out.mem (table + j) =
          Chain.concreteLevelRebuildCount M C.k a (concreteThresholdScale C.d) j (4 * M) ∧
        (out.mem (table + j) : ℝ) ≤
          Chain.SparseCoreTool.updateThreshold C.k
            (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ∧
        Chain.SparseCoreTool.updateThreshold C.k
            (Chain.levelM (SparseCore.sparseCoreParams E) C j) (4 * M) ≤
          48 * ((out.mem (table + j) : ℝ) + 1)) ∧
      RebuiltCoresAt R chain out.mem levelTable (levelTable + (C.d + 1)) 0 C.d finalHeap ∧
      out.mem (levelTable + (C.d + 1) + C.d) = chain.lastBran ∧
      (∃ y : terminal.τ, terminal.rep (out.mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs)
        y out.mem ∧ ∀ addr, terminal.foot (out.mem (levelTable + C.d)) y addr → addr < finalHeap) ∧
      (∀ addr, levelsEnd ≤ addr → addr < freshCounter → out.mem addr = 0) ∧
      FreshTablesAt out.mem forward inverse freshCounter I.m I.m id id I.m ∧
      Rtree.rep treeHeap sTree xTree out.mem ∧
      ZeroFrom out.mem finalHeap ∧ heap ≤ finalHeap ∧
      (∀ x < heap, out.mem x = mem x)
  obtain ⟨out, cost, table, a, hrun, hpost⟩ :=
    hprefix J E (Post := Post) hJn hJm hcap hIvalid hk hheapPow hqw hcmult hM
      hqual halpha hselect hpack hdepthProc hclog hfactorImpl hpower hext hmul hshift hadd
      hGraph hGraphBelow hz hEL hGrowth hK1 hps1 hCoeff hγM hγk hBfn hDegree
      (levels := buildSolverInitLevels init (op 3) (op 2) copy sort entry terminalInit ;;
        finishSolverInitBody treeInit)
      (inconclusive := inconclusive)
      (fun table a header h74 h77 hroomH _ hzH hchainH hnumH htableH htableGe hGdgH
          _ _ _ hframeH h67H h68H h69H h70H h71H h75H => by
        have hLenH : EdgeValuesAt header.mem lengths 4 L P G.E len₀ :=
          hLenMem.congr (fun e he j hj =>
            hframeH _ (tail_vec_lt_heap (hGm ▸ Finset.mem_range.mp he) hj hLenEnd))
        have hGradH : EdgeValuesAt header.mem gradient 4 L P G.E grad₀ :=
          hGradMem.congr (fun e he j hj =>
            hframeH _ (tail_vec_lt_heap (hGm ▸ Finset.mem_range.mp he) hj hGradEnd))
        obtain ⟨mid, levCost, hrLev, hcoresM, hbrM, hzeroM, hlevGe, ⟨yTerm, hrepTermM, hfootTermM⟩, hframeL, _⟩ :=
          buildSolverInitLevels_fixedPoint_runs (fmt := fmt) (ω := ω)
            oracle C_lsst scDepth sparsify (P := C) (R := R) (terminal := terminal)
            G len₀ grad₀ h77 h69H h71H h70H h75H h67H h68H hzH hroomH
            hGdgH hLenH hGradH
            (htableGe.trans ((Nat.le_add_right _ _).trans (Nat.le_add_right _ _)))
            (tail_le_heap_to_le_levelTable hLenEnd htableGe)
            (tail_le_heap_to_le_levelTable hGradEnd htableGe)
            hfit.2.1 hfit.2.2.1 rfl hWidth4 hdW hkW hw9 hlocal hcopy hsort hentry
            hNconst hValidLast hcoreImpl htermImpl hmodel (fun ω' => hreadout ω' (table + (C.d + 1) + 17))
            hstretch hposLast (hspaceLast (table + (C.d + 1) + 17))
        have hg3 : 3 ≤ dynGraphSize G.n G.m := by unfold dynGraphSize; omega
        have hmMid : mid.mem (table + (C.d + 1) + 9) = I.m :=
          (hframeL _ (tail_handle_chain_lt_levelTable (by decide : 0 < 8))).trans
            (by simpa [Nat.add_assoc] using hchainH 0 (by simp))
        have hnMid : mid.mem (heap + (L + 1) + 6 + 2) = G.n :=
          (hframeL _ (tail_root_n_lt_levelTable hg3 htableGe)).trans hGdgH.2.2.2.2.2.1
        have hnumMid : MinRatioNumericHeaderAt mid.mem (table + (C.d + 1)) L P
            (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) := by
          intro j hj
          have hj4 : j < 4 := by simpa [List.length] using hj
          exact (hframeL _ (tail_handle_num_lt_levelTable hj4)).trans (hnumH j hj)
        have hchainMid : ChainInitParametersAt mid.mem (table + (C.d + 1)) I.m V C.d C.k Ψ heap k epsExp := by
          intro j hj
          have hj8 : j < 8 := by simpa [List.length] using hj
          exact (hframeL _ (tail_handle_chain_lt_levelTable hj8)).trans (hchainH j hj)
        have h74M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h74
        have h75M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h75H
        have h69M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h69H
        have h67M := (buildSolverInitLevels_preserves_regs (by decide) (by decide) hrLev).trans h67H
        obtain ⟨out, tailCost, sTree, xTree, finalHeap, hrTail, _, _, _, _, _, _, _, h99Out,
            hdetectOut, hnumOut, hschedZero, hfreshOut, hrepTreeOut, _, hzFinal, htreeLeFinal, _,
            _, hframeTail, _⟩ :=
          finishSolverInitBody_runs (fmt := fmt) (ω := ω) (st := mid)
            h74M h75M h69M h67M rfl hmMid hnMid hnumMid hzeroM
            (tail_handle_end_lt_lev hlevGe) (tail_root_n_lt_lev hg3 htableGe hlevGe)
            htreeImpl hfit.2.1 hfit.2.2.1 hnWord hnFit
            (htreeSpace (table + (C.d + 1) + 17) mid hcoresM) hw16
        have hlevLeFinal : mid.regs 4 ≤ finalHeap :=
          (tail_lev_le_treeHeap (mid.regs 4) C.d I.m).trans htreeLeFinal
        refine ⟨out, levCost + tailCost + 1,
          runs_seq_iff.mpr (Or.inr ⟨mid, levCost, tailCost, hrLev, hrTail, rfl⟩),
          mid.regs 4, finalHeap, sTree, xTree, h99Out, hdetectOut, ?_, hnumOut, ?_, ?_, ?_, ?_,
          hschedZero, hfreshOut, hrepTreeOut, hzFinal,
          tail_heap_le_final htableGe hlevGe hlevLeFinal,
          fun x hx => by
            obtain ⟨hx1, hx2, hx3⟩ := tail_x_lt_lev hx htableGe hlevGe
            exact (hframeTail x hx1 (Or.inl hx2)).trans ((hframeL x hx3).trans (hframeH x hx))⟩
        · intro j hj
          have hj8 : j < 8 := by simpa [List.length] using hj
          obtain ⟨h1, h2⟩ := tail_chain_in_lev hj8 hlevGe
          exact (hframeTail _ h1 (Or.inr h2)).trans (hchainMid j hj)
        · intro j hj
          obtain ⟨h1, h2, h3⟩ := tail_table_in_lev hj hlevGe
          have htj : out.mem (table + j) = header.mem (table + j) :=
            (hframeTail _ h1 (Or.inl h2)).trans (hframeL _ h3)
          have hej := htableH j hj
          refine ⟨htj.trans hej.1, ?_, ?_⟩
          · rw [htj]; exact hej.2.1
          · rw [htj]; exact hej.2.2
        · intro j hj hlt
          obtain ⟨hbj, xj, hrepj, hhGt, hbGt, hfootj⟩ := hcoresM j hj hlt
          obtain ⟨hc1, hc2, hb1, hb2⟩ := tail_core_cell_in_lev hlt.le hlevGe
          have hcellAgree : out.mem (table + (C.d + 1) + 17 + j) = mid.mem (table + (C.d + 1) + 17 + j) :=
            hframeTail _ hc1 (Or.inr hc2)
          have hbrAgree : out.mem (table + (C.d + 1) + 17 + (C.d + 1) + j) =
              mid.mem (table + (C.d + 1) + 17 + (C.d + 1) + j) :=
            hframeTail _ hb1 (Or.inr hb2)
          refine ⟨hbrAgree.trans hbj, xj, ?_, hcellAgree.symm ▸ hhGt, hcellAgree.symm ▸ hbGt, ?_⟩
          · rw [hcellAgree]
            refine (hlocal _ _ _ mid.mem out.mem ?_).1 hrepj
            intro a ha
            obtain ⟨hloA, hltA⟩ := hfootj a ha
            exact (hframeTail a hltA (Or.inr (tail_foot_above_desc hhGt hloA))).symm
          · intro a ha
            rw [hcellAgree] at ha ⊢
            obtain ⟨hloA, hltA⟩ := hfootj a ha
            exact ⟨hloA, hltA.trans_le hlevLeFinal⟩
        · obtain ⟨_, _, hb1, hb2⟩ := tail_core_cell_in_lev le_rfl hlevGe
          exact (hframeTail _ hb1 (Or.inr hb2)).trans hbrM
        · obtain ⟨hc1, hc2, _, _⟩ := tail_core_cell_in_lev le_rfl hlevGe
          have hc : out.mem (table + (C.d + 1) + 17 + C.d) = mid.mem (table + (C.d + 1) + 17 + C.d) :=
            hframeTail _ hc1 (Or.inr hc2)
          refine ⟨yTerm, ?_, fun a ha => by
            rw [hc] at ha
            exact (hfootTermM a ha).2.trans_le hlevLeFinal⟩
          rw [hc]
          refine (htermLocal _ _ _ mid.mem out.mem ?_).1 hrepTermM
          intro a ha
          obtain ⟨hloA, hltA⟩ := hfootTermM a ha
          exact (hframeTail a hltA (Or.inr (tail_term_foot_above_desc hloA))).symm)
  obtain ⟨levelsEnd, finalHeap, sTree, xTree, h99, hrest⟩ := hpost
  have hret : Runs w p ω (.ret (.reg 99)) out (.returned finalHeap) out 2 :=
    runs_ret_iff.mpr ⟨finalHeap, by simp [Expr.eval, h99], rfl, rfl, rfl⟩
  exact ⟨out, cost + 2 + 1, table, a, levelsEnd, finalHeap, sTree, xTree,
    runs_seq_iff.mpr (Or.inr ⟨out, cost, 2, hrun, hret, rfl⟩), hrest⟩

end MinCostFlow.MinRatio
