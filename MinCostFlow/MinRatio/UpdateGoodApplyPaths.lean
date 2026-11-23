module

public import MinCostFlow.MinRatio.SolverRep
public import MinCostFlow.MinRatio.PathNumericHistory
public import MinCostFlow.MinRatio.PathTreeCall
public import MinCostFlow.LinkCut.PathProg.Account
import MinCostFlow.MinRatio.TreeEdit
import WordRAM.Tactic

/-!
# Tree-path flow and detector application loop for `Update`

When `Chain.Ordered.algorithm2_loopWith` selects a good cycle whose tree component is given as a list
of cancellation-free endpoint pairs `paths : List (ℕ × ℕ)` (0-based vertex indices stored
at `pathsBase`), `updateGoodApplyPathsBody` applies `PathTag.ofFlow multiplier` to each
tree path `(u + 1, v + 1)` via Section 6 `opTree 2` (`PathApply`).

Proves `updateGoodApplyPathsBody_runs`, showing exact folding of `lctPathApply`,
preservation of `LctInvWith`, `PathTreeNumericInv` (incremented by `paths.length * pathTagMagnitude tag`),
tree connectivity, memory framing outside the path-tree footprint, and amortized cost
`≤ paths.length * (pathTreeBudget PathProg.pathC L tree.n + 45) + 30`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain

/-- Packed array of `paths.length` vertex-pair endpoints `[u_0, v_0, u_1, v_1, ...]`
at `[base, base + 2 * paths.length)`. -/
@[expose] def PathEndpointsAt (mem : ℕ → ℕ) (base : ℕ) (paths : List (ℕ × ℕ)) : Prop :=
  ∀ j (hj : j < paths.length),
    mem (base + 2 * j) = (paths[j]'hj).1 ∧ mem (base + 2 * j + 1) = (paths[j]'hj).2

/-- Space allocated by a single Section 6 `PathApply` call (`opTree 2`). -/
@[expose] def pathApplySpace (L : ℕ) : ℕ :=
  20 * LinkCut.PathProg.treeLimbs L + 100

/-- Fixed deterministic loop applying `PathApply` (`opTree 2`) to each endpoint pair
`(u_j, v_j)` in `pathsBase[0 .. pathsLen)`. Arguments: `[root, pathsBase, pathsLen, tagPtr, heap]`. -/
@[expose] def updateGoodApplyPathsBody (pathApply : ℕ) : Stmt :=
  .assign 5 (.load (.load (.reg 0))) ;;
  .assign 6 (.reg 4) ;;
  forRange 7 (.const 0) (.reg 2)
    (.assign 8 (.bin .add (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 7)))) (.const 1)) ;;
     .assign 9 (.bin .add (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 7))) (.const 1))) (.const 1)) ;;
     .call 6 pathApply [.reg 5, .reg 8, .reg 9, .reg 3, .reg 6]) ;;
  .ret (.reg 6)

theorem updateGoodApplyPathsBody_noRand (pathApply : ℕ) :
    (updateGoodApplyPathsBody pathApply).NoRand := by
  simp [updateGoodApplyPathsBody, forRange, forUp, Stmt.NoRand]

/-- Fold `lctPathApply` over a list of 0-based vertex pairs. -/
@[expose] def applyPathsFold (s : PathTreeState) (tag : PathTag) (paths : List (ℕ × ℕ)) :
    PathTreeState :=
  paths.foldl (fun cur p => lctPathApply pathPayload cur (p.1 + 1) (p.2 + 1) tag) s

private theorem applyPathsFold_cons (s : PathTreeState) (tag : PathTag)
    (p : ℕ × ℕ) (rest : List (ℕ × ℕ)) :
    applyPathsFold s tag (p :: rest) =
      applyPathsFold (lctPathApply pathPayload s (p.1 + 1) (p.2 + 1) tag) tag rest := rfl

/-- Helper: inductive execution of the `while (reg 7 < reg 2)` loop inside `updateGoodApplyPathsBody`. -/
private theorem updateGoodApplyPathsLoop_runs
    {w L initTree treeHeap pathsBase tagPtr heap0 : ℕ}
    {fmt : Num.Format w} {opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool}
    {paths : List (ℕ × ℕ)} {tag : PathTag}
    (hfmt4 : fmt.limbBits = 4)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hw1 : 1 < 2 ^ w) (h2W : 2 < 2 ^ w)
    (hpathsLenW : paths.length < 2 ^ w)
    (hpathsEnd : pathsBase + 2 * paths.length ≤ heap0)
    (htagEnd : tagPtr + 2 * L ≤ heap0)
    (hroom : heap0 + paths.length * pathApplySpace L < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    ∀ (rem : ℕ) (st : State) (s : PathTreeState) (trees : List AuxTree) (free : List ℕ)
      (depth : ℕ → ℕ) (treeTok : Rtree.τ) (B R : ℤ),
      let j := paths.length - rem
      rem ≤ paths.length →
      st.regs 1 = pathsBase → st.regs 2 = paths.length → st.regs 3 = tagPtr →
      st.regs 5 = treeHeap → heap0 ≤ st.regs 6 →
      st.regs 6 ≤ heap0 + j * pathApplySpace L →
      st.regs 7 = j →
      treeHeap < 2 ^ w → 2 * s.n + 1 < 2 ^ w → Nat.log 2 (2 * s.n + 1) ≤ 4 * L →
      LctInvWith pathPayload s trees free depth →
      PathTreeNumericInv s trees B R →
      2 * ((2 * s.n + 1 : ℕ) : ℤ) * ((B + (rem : ℤ) * pathTagMagnitude tag) +
        (R + (rem : ℤ) * pathTagMagnitude tag)) < (Num.capacity 4 L : ℤ) →
      Rtree.rep treeHeap s treeTok st.mem →
      (∀ a, Rtree.foot treeHeap treeTok a → a < st.regs 6) →
      (∀ a, Rtree.foot treeHeap treeTok a →
        (a < pathsBase ∨ pathsBase + 2 * paths.length ≤ a) ∧
        (a < tagPtr ∨ tagPtr + 2 * L ≤ a)) →
      PathEndpointsAt st.mem pathsBase paths →
      PathTagAt st.mem tagPtr 4 L tag →
      (∀ k (hk : k < paths.length), j ≤ k →
        (paths[k]'hk).1 < s.n ∧ (paths[k]'hk).2 < s.n ∧
        pathTreeConnected s ((paths[k]'hk).1 + 1) ((paths[k]'hk).2 + 1)) →
      ZeroFrom st.mem (st.regs 6) →
      ∃ out cost ret trees' depth' treeTok',
        Runs w p ω
          (.loop (.bin .lt (.reg 7) (.reg 2))
            ((.assign 8 (.bin .add (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 7)))) (.const 1)) ;;
              .assign 9 (.bin .add (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 7))) (.const 1))) (.const 1)) ;;
              .call 6 (opTree 2) [.reg 5, .reg 8, .reg 9, .reg 3, .reg 6]) ;;
             .assign 7 (.bin .add (.reg 7) (.const 1))))
          st .normal out cost ∧
        out.regs 6 = ret ∧ st.regs 6 ≤ ret ∧
        ret ≤ heap0 + paths.length * pathApplySpace L ∧
        let s' := applyPathsFold s tag (paths.drop j)
        LctInvWith pathPayload s' trees' free depth' ∧
        PathTreeNumericInv s' trees' (B + (rem : ℤ) * pathTagMagnitude tag)
          (R + (rem : ℤ) * pathTagMagnitude tag) ∧
        Rtree.rep treeHeap s' treeTok' out.mem ∧
        ZeroFrom out.mem ret ∧
        (∀ a < st.regs 6, ¬ Rtree.foot treeHeap treeTok a → out.mem a = st.mem a) ∧
        (∀ a, Rtree.foot treeHeap treeTok' a → Rtree.foot treeHeap treeTok a ∨ (st.regs 6 ≤ a ∧ a < ret)) ∧
        cost + Rtree.phi treeHeap treeTok' out.mem ≤
          rem * (pathTreeBudget LinkCut.PathProg.pathC L s.n + 45) + 4 +
          Rtree.phi treeHeap treeTok st.mem := by
  intro Rtree rem
  induction rem with
  | zero =>
    intro st s trees free depth treeTok B R j hrem hr1 hr2 hr3 hr5 hheapLo hheapHi hr7
      htreeW h2nW hlogW hW hnum hcap hrep hfoot hsep hends htag hconn hz
    have hjEq : j = paths.length := by dsimp only [j]; omega
    have hdrop : paths.drop j = [] := List.drop_eq_nil_of_le (by omega)
    have hcond0 : (Expr.bin .lt (.reg 7) (.reg 2)).eval w st = some 0 := by
      simp [Expr.eval, BinOp.eval, hr7, hr2, hjEq, show 0 < 2 ^ w by omega]
    refine ⟨st, 4, st.regs 6, trees, depth, treeTok,
      runs_loop_iff.mpr (Or.inl ⟨hcond0, rfl, rfl, by simp [Expr.size]⟩),
      rfl, le_rfl, by rw [hjEq] at hheapHi; exact hheapHi,
      by simp [hdrop, applyPathsFold]; exact hW,
      by simp [hdrop, applyPathsFold]; exact hnum,
      by simp [hdrop, applyPathsFold]; exact hrep,
      hz, fun _ _ _ => rfl, fun _ ha => Or.inl ha, by omega⟩
  | succ rem ih =>
    intro st s trees free depth treeTok B R j hrem hr1 hr2 hr3 hr5 hheapLo hheapHi hr7
      htreeW h2nW hlogW hW hnum hcap hrep hfoot hsep hends htag hconn hz
    have hjLt : j < paths.length := by dsimp only [j]; omega
    have hremNext : paths.length - rem = j + 1 := by dsimp only [j]; omega
    have hcurHeapW : st.regs 6 < 2 ^ w := by
      have : j * pathApplySpace L ≤ paths.length * pathApplySpace L := Nat.mul_le_mul_right _ hjLt.le
      omega
    obtain ⟨huLt, hvLt, hconnJ⟩ := hconn j hjLt le_rfl
    obtain ⟨hmU, hmV⟩ := hends j hjLt
    let u := (paths[j]'hjLt).1
    let v := (paths[j]'hjLt).2
    let u1 := u + 1
    let v1 := v + 1
    let curHeap := st.regs 6
    have hu1W : u1 < 2 ^ w := by dsimp only [u1, u]; omega
    have hv1W : v1 < 2 ^ w := by dsimp only [v1, v]; omega
    have h2jW : 2 * j < 2 ^ w := by omega
    have hp2jW : pathsBase + 2 * j < 2 ^ w := by omega
    have hp2j1W : pathsBase + 2 * j + 1 < 2 ^ w := by omega
    -- Step 1: evaluate `reg 8 := mem (pathsBase + 2 * j) + 1`, `reg 9 := mem (pathsBase + 2 * j + 1) + 1`
    let s1 : State := { st with regs := Function.update st.regs 8 u1 }
    let s2 : State := { s1 with regs := Function.update s1.regs 9 v1 }
    have r1 : Runs w p ω (.assign 8 (.bin .add (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 7)))) (.const 1)))
        st .normal s1 9 :=
      runs_assign_iff.mpr ⟨u1, by
        simp [Expr.eval, BinOp.eval, hr1, hr7, h2W, hw1, h2jW, hp2jW, hmU, hu1W, u1, u], rfl, rfl, rfl⟩
    have r2 : Runs w p ω (.assign 9 (.bin .add (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 7))) (.const 1))) (.const 1)))
        s1 .normal s2 11 :=
      runs_assign_iff.mpr ⟨v1, by
        simp [Expr.eval, BinOp.eval, s1, hr1, hr7, h2W, hw1, h2jW, hp2jW, hp2j1W, hmV, hv1W, v1, v],
        rfl, rfl, rfl⟩
    -- Step 2: discharge `opTree 2` (`PathApply`) precondition via `PathTreeNumericInv`
    have htagNN : 0 ≤ pathTagMagnitude tag := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hcapCur : 2 * ((2 * s.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ) := by
      have h1 : B + R ≤ (B + ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag) +
          (R + ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag) := by
        have hpos : (0 : ℤ) ≤ ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag :=
          mul_nonneg (Nat.cast_nonneg _) htagNN
        omega
      have hmul : 2 * ((2 * s.n + 1 : ℕ) : ℤ) * (B + R) ≤
          2 * ((2 * s.n + 1 : ℕ) : ℤ) * ((B + ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag) +
            (R + ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag)) :=
        mul_le_mul_of_nonneg_left h1 (by positivity)
      omega
    have hfitCur : pathTreeFits 4 L s := hnum.fits hW hcapCur
    obtain ⟨tu, htu, huIn⟩ := List.mem_flatMap.mp (hW.verticesActive u huLt)
    obtain ⟨tv, htv, hvIn⟩ := List.mem_flatMap.mp (hW.verticesActive v hvLt)
    have hrootsEq : subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length (vid u) =
        subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length (vid v) :=
      (pathTreeConnected_iff_induced_roots hW huLt hvLt).mp hconnJ
    obtain ⟨trees1, depth1, hW1, hnum1⟩ := pathTreeNumericInv_apply hW hnum htu huIn
      (show isVertex s.n u1 from ⟨by dsimp [u1]; omega, by dsimp [u1]; omega⟩)
      htv hvIn (show isVertex s.n v1 from ⟨by dsimp [v1]; omega, by dsimp [v1]; omega⟩) hrootsEq tag
    have hnextN : (lctPathApply pathPayload s u1 v1 tag).n = s.n := rfl
    have hcapNext : 2 * ((2 * (lctPathApply pathPayload s u1 v1 tag).n + 1 : ℕ) : ℤ) *
        ((B + pathTagMagnitude tag) + (R + pathTagMagnitude tag)) < (Num.capacity 4 L : ℤ) := by
      rw [hnextN]
      have h1 : (B + pathTagMagnitude tag) + (R + pathTagMagnitude tag) ≤
          (B + ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag) +
            (R + ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag) := by
        have hpos : (0 : ℤ) ≤ (rem : ℤ) * pathTagMagnitude tag := mul_nonneg (Nat.cast_nonneg _) htagNN
        push_cast; nlinarith
      have hmul := mul_le_mul_of_nonneg_left h1 (show (0 : ℤ) ≤ 2 * ((2 * s.n + 1 : ℕ) : ℤ) by positivity)
      omega
    have hfitNext : pathTreeFits 4 L (lctPathApply pathPayload s u1 v1 tag) := hnum1.fits hW1 hcapNext
    have htagAt2 : PathTagAt s2.mem tagPtr fmt.limbBits L tag := by rw [hfmt4]; exact htag
    have hpre2 : (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)).pre
        2 s [treeHeap, u1, v1, tagPtr, curHeap] s2.mem := by
      refine ⟨⟨trees, free, depth, hW⟩, hfmt4.symm ▸ hfitCur, h2nW, hfmt4.symm ▸ hlogW,
        treeHeap, u1, v1, tagPtr, curHeap, rfl,
        ⟨by dsimp [u1]; omega, by dsimp [u1]; omega⟩,
        ⟨by dsimp [v1]; omega, by dsimp [v1]; omega⟩,
        hconnJ, le_trans htagEnd hheapLo,
        by rw [readPathTag_eq htagAt2]; exact htagAt2,
        by rw [readPathTag_eq htagAt2, hfmt4]; exact hfitNext⟩
    have hroomStep : curHeap + LinkCut.PathProg.pathAlloc L 2 s.n [treeHeap, u1, v1, tagPtr, curHeap] < 2 ^ w := by
      simp only [LinkCut.PathProg.pathAlloc, show (2 : ℕ) ≠ 7 by decide, ↓reduceIte]
      have hle : (j + 1) * pathApplySpace L ≤ paths.length * pathApplySpace L := Nat.mul_le_mul_right _ hjLt
      rw [Nat.add_mul, one_mul] at hle
      dsimp only [pathApplySpace] at hheapHi hle hroom ⊢; omega
    obtain ⟨sNext, cTree, after, treeTok1, ret1, hrTree, hrep1, hpost1, hresp1, hcTree⟩ :=
      pathTree_runs_call (ω := ω) (st := s2) (reg := 6) (i := 2) (b := treeHeap)
        (args := [.reg 5, .reg 8, .reg 9, .reg 3, .reg 6]) (vs := [treeHeap, u1, v1, tagPtr, curHeap])
        hTreeImpl (by simp [evalArgs, Expr.eval, s2, s1, hr5, hr3, curHeap])
        (by intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega)
        rfl hrep hpre2 hfoot hz hroomStep
    have hsNextEq : sNext = lctPathApply pathPayload s u1 v1 tag :=
      pathTreeMachineContract_apply_state htagAt2 hpost1
    subst hsNextEq
    let s3 : State := { after with regs := Function.update s2.regs 6 ret1 }
    let s4 : State := { s3 with regs := Function.update s3.regs 7 (j + 1) }
    have rInc : Runs w p ω (.assign 7 (.bin .add (.reg 7) (.const 1))) s3 .normal s4 4 :=
      runs_assign_iff.mpr ⟨j + 1, by
        simp [Expr.eval, BinOp.eval, s3, s2, s1, hr7, hw1, show j + 1 < 2 ^ w by omega],
        rfl, rfl, rfl⟩
    have hstepRun : Runs w p ω
        ((.assign 8 (.bin .add (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 7)))) (.const 1)) ;;
          .assign 9 (.bin .add (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 7))) (.const 1))) (.const 1)) ;;
          .call 6 (opTree 2) [.reg 5, .reg 8, .reg 9, .reg 3, .reg 6]) ;;
         .assign 7 (.bin .add (.reg 7) (.const 1))) st .normal s4 ((9 + (11 + cTree + 1) + 1) + 4 + 1) :=
      runs_seq_iff.mpr (Or.inr ⟨s3, 9 + (11 + cTree + 1) + 1, 4,
        runs_seq_iff.mpr (Or.inr ⟨s1, 9, 11 + cTree + 1, r1,
          runs_seq_iff.mpr (Or.inr ⟨s2, 11, cTree, r2, hrTree, rfl⟩), rfl⟩), rInc, rfl⟩)
    -- Transfer invariants to `s4`
    obtain ⟨hret1Lo, hret1Hi, hz1, hfr1, hft1⟩ := hresp1
    change curHeap ≤ ret1 at hret1Lo
    change ret1 ≤ curHeap + LinkCut.PathProg.pathAlloc L 2 s.n [treeHeap, u1, v1, tagPtr, curHeap] at hret1Hi
    change ∀ a < curHeap, ¬ Rtree.foot treeHeap treeTok a → after.mem a = s2.mem a at hfr1
    change ∀ a, Rtree.foot treeHeap treeTok1 a → Rtree.foot treeHeap treeTok a ∨ (curHeap ≤ a ∧ a < ret1) at hft1
    simp only [LinkCut.PathProg.pathAlloc, show (2 : ℕ) ≠ 7 by decide, ↓reduceIte] at hret1Hi
    have hret1Le : ret1 ≤ heap0 + (j + 1) * pathApplySpace L := by
      rw [Nat.add_mul, one_mul]; dsimp only [pathApplySpace] at hheapHi ⊢; omega
    have hsep1 : ∀ a, Rtree.foot treeHeap treeTok1 a →
        (a < pathsBase ∨ pathsBase + 2 * paths.length ≤ a) ∧
        (a < tagPtr ∨ tagPtr + 2 * L ≤ a) := fun a ha => by
      rcases hft1 a ha with h0 | ⟨hlo, _⟩
      · exact hsep a h0
      · exact ⟨Or.inr (by omega), Or.inr (by omega)⟩
    have hfoot1 : ∀ a, Rtree.foot treeHeap treeTok1 a → a < ret1 := fun a ha => by
      rcases hft1 a ha with h0 | ⟨_, hhi⟩
      · exact lt_of_lt_of_le (hfoot a h0) hret1Lo
      · exact hhi
    have hends1 : PathEndpointsAt s4.mem pathsBase paths := fun k hk => by
      have hm1 := hfr1 (pathsBase + 2 * k) (by omega) (fun hf => by have := (hsep _ hf).1; omega)
      have hm2 := hfr1 (pathsBase + 2 * k + 1) (by omega) (fun hf => by have := (hsep _ hf).1; omega)
      exact ⟨hm1.trans (hends k hk).1, hm2.trans (hends k hk).2⟩
    have htag1 : PathTagAt s4.mem tagPtr 4 L tag :=
      ⟨htag.1.congr (fun i hi => hfr1 (tagPtr + i) (by omega) (fun hf => by have := (hsep _ hf).2; omega)),
       htag.2.congr (fun i hi => hfr1 (tagPtr + L + i) (by omega) (fun hf => by have := (hsep _ hf).2; omega))⟩
    -- Connectivity preserved across `lctPathApply` via `lctPathApply_spec`
    have hconn1 : ∀ k (hk : k < paths.length), j + 1 ≤ k →
        (paths[k]'hk).1 < (lctPathApply pathPayload s u1 v1 tag).n ∧
        (paths[k]'hk).2 < (lctPathApply pathPayload s u1 v1 tag).n ∧
        pathTreeConnected (lctPathApply pathPayload s u1 v1 tag) ((paths[k]'hk).1 + 1) ((paths[k]'hk).2 + 1) := by
      obtain ⟨tsSpec, _, dSpec, _, hWSpec, _, _, _, _, _, _, _, _, _, _, hconnIff, _, _⟩ :=
        lctPathApply_spec pathPayload_laws hW htu huIn
          (show isVertex s.n u1 from ⟨by dsimp [u1]; omega, by dsimp [u1]; omega⟩) htv hvIn hrootsEq tag
      intro k hk hjk
      obtain ⟨ha1, ha2, hck⟩ := hconn k hk (by omega)
      refine ⟨hnextN.symm ▸ ha1, hnextN.symm ▸ ha2, ?_⟩
      have hrootOld := (pathTreeConnected_iff_induced_roots hW ha1 ha2).mp hck
      have hrootNew := (hconnIff (vid (paths[k]'hk).1) (hW.verticesActive _ ha1)
        (vid (paths[k]'hk).2) (hW.verticesActive _ ha2)).mpr hrootOld
      exact (pathTreeConnected_iff_induced_roots hWSpec (hnextN.symm ▸ ha1) (hnextN.symm ▸ ha2)).mpr hrootNew
    have hcapRem : 2 * ((2 * (lctPathApply pathPayload s u1 v1 tag).n + 1 : ℕ) : ℤ) *
        (((B + pathTagMagnitude tag) + (rem : ℤ) * pathTagMagnitude tag) +
          ((R + pathTagMagnitude tag) + (rem : ℤ) * pathTagMagnitude tag)) < (Num.capacity 4 L : ℤ) := by
      rw [hnextN]
      have heq : ((B + pathTagMagnitude tag) + (rem : ℤ) * pathTagMagnitude tag) +
          ((R + pathTagMagnitude tag) + (rem : ℤ) * pathTagMagnitude tag) =
          (B + ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag) +
          (R + ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag) := by push_cast; ring
      rw [heq]; exact hcap
    -- Recurse on `rem`
    obtain ⟨out, cRest, ret, trees', depth', treeTok', hrRest, hretR6, hretLo2, hretHi2,
        hW', hnum', hrep', hz', hfrRest, hftRest, hcRest⟩ :=
      ih s4 (lctPathApply pathPayload s u1 v1 tag) trees1 free depth1 treeTok1
        (B + pathTagMagnitude tag) (R + pathTagMagnitude tag) (by omega)
        (by simp [s4, s3, s2, s1, hr1]) (by simp [s4, s3, s2, s1, hr2])
        (by simp [s4, s3, s2, s1, hr3]) (by simp [s4, s3, s2, s1, hr5])
        (by simp [s4, s3]; exact le_trans hheapLo hret1Lo)
        (by simp [s4, s3, hremNext]; exact hret1Le)
        (by simp [s4, hremNext])
        htreeW (by rw [hnextN]; exact h2nW) (by rw [hnextN]; exact hlogW)
        hW1 hnum1 hcapRem hrep1 (by simp [s4, s3]; exact hfoot1) hsep1 hends1 htag1
        (by simp only [hremNext]; exact hconn1) (by simp [s4, s3]; exact hz1)
    have hdropSplit : paths.drop j = (paths[j]'hjLt) :: paths.drop (j + 1) :=
      List.drop_eq_getElem_cons hjLt
    have hfoldEq : applyPathsFold s tag (paths.drop j) =
        applyPathsFold (lctPathApply pathPayload s u1 v1 tag) tag (paths.drop (paths.length - rem)) := by
      rw [hdropSplit, applyPathsFold_cons, hremNext]
    have hB_eq : B + ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag =
        B + pathTagMagnitude tag + (rem : ℤ) * pathTagMagnitude tag := by push_cast; ring
    have hR_eq : R + ((rem + 1 : ℕ) : ℤ) * pathTagMagnitude tag =
        R + pathTagMagnitude tag + (rem : ℤ) * pathTagMagnitude tag := by push_cast; ring
    have hcond1 : (Expr.bin .lt (.reg 7) (.reg 2)).eval w st = some 1 := by
      simp [Expr.eval, BinOp.eval, hr7, hr2, hjLt, hw1]
    have hrLoop : Runs w p ω
        (.loop (.bin .lt (.reg 7) (.reg 2))
          ((.assign 8 (.bin .add (.load (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 7)))) (.const 1)) ;;
            .assign 9 (.bin .add (.load (.bin .add (.bin .add (.reg 1) (.bin .mul (.const 2) (.reg 7))) (.const 1))) (.const 1)) ;;
            .call 6 (opTree 2) [.reg 5, .reg 8, .reg 9, .reg 3, .reg 6]) ;;
           .assign 7 (.bin .add (.reg 7) (.const 1))))
        st .normal out (3 + ((9 + (11 + cTree + 1) + 1) + 4 + 1) + cRest + 1) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s4, _, cRest, hcond1, by decide, hstepRun, hrRest,
        by simp [Expr.size]⟩))
    refine ⟨out, _, ret, trees', depth', treeTok', hrLoop, hretR6,
      le_trans hret1Lo (by simpa [s4, s3] using hretLo2), hretHi2,
      by rw [hfoldEq]; exact hW',
      by rw [hfoldEq, hB_eq, hR_eq]; exact hnum',
      by rw [hfoldEq]; exact hrep', hz', ?_, ?_, ?_⟩
    · intro a ha hnf
      have hnf1 : ¬ Rtree.foot treeHeap treeTok1 a := fun h => by
        rcases hft1 a h with h0 | ⟨hlo, _⟩
        · exact hnf h0
        · omega
      exact (hfrRest a (by simp [s4, s3]; exact lt_of_lt_of_le ha hret1Lo) hnf1).trans
        (hfr1 a ha hnf)
    · intro a ha
      rcases hftRest a ha with h1 | ⟨hlo, hhi⟩
      · rcases hft1 a h1 with h0 | ⟨hlo0, hhi0⟩
        · exact Or.inl h0
        · exact Or.inr ⟨hlo0, lt_of_lt_of_le hhi0 (by simpa [s4, s3] using hretLo2)⟩
      · exact Or.inr ⟨le_trans hret1Lo (by simpa [s4, s3] using hlo), hhi⟩
    · have hargSz : argsSize [.reg 5, .reg 8, .reg 9, .reg 3, .reg 6] = 5 := by
        simp [argsSize, Expr.size]
      rw [hargSz] at hcTree
      rw [hnextN] at hcRest
      change _ + Rtree.phi treeHeap treeTok' out.mem ≤
        (rem + 1) * (pathTreeBudget LinkCut.PathProg.pathC L s.n + 45) + 4 +
        Rtree.phi treeHeap treeTok st.mem
      rw [Nat.add_mul, one_mul]
      dsimp only [Rtree, s4, s3, s2, s1] at hcTree hcRest ⊢
      omega

/-- End-to-end execution of `updateGoodApplyPathsBody`, updating the path tree across all
`paths` while preserving `solverStateRep`'s other regions and advancing `PathTreeNumericInv`. -/
theorem updateGoodApplyPathsBody_runs
    {w L P m V psi k epsExp drainUnit initTree root pathsBase tagPtr heap pos : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {opTree : ℕ → ℕ} {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore}
    {paths : List (ℕ × ℕ)} {tag : PathTag} {B R : ℤ}
    (hfmt4 : fmt.limbBits = 4)
    (hTreeImpl : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).Implements w p initTree opTree
      (pathTreeMachineContract fmt L LinkCut.PathProg.pathC (LinkCut.PathProg.pathAlloc L)))
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem)
    (hnum : PathTreeNumericInv tok.tree tok.trees B R)
    (hbelow : ∀ a, (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).foot root tok a → a < heap)
    (hpathsEnd : pathsBase + 2 * paths.length ≤ heap)
    (htagEnd : tagPtr + 2 * L ≤ heap)
    (hsepTree : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a →
      (a < pathsBase ∨ pathsBase + 2 * paths.length ≤ a) ∧
      (a < tagPtr ∨ tagPtr + 2 * L ≤ a))
    (hends : PathEndpointsAt mem pathsBase paths)
    (htagAt : PathTagAt mem tagPtr 4 L tag)
    (hconn : ∀ q ∈ paths, q.1 < tok.tree.n ∧ q.2 < tok.tree.n ∧
      pathTreeConnected tok.tree (q.1 + 1) (q.2 + 1))
    (hz : ZeroFrom mem heap)
    (hw2 : 2 < 2 ^ w) (h2nW : 2 * tok.tree.n + 1 < 2 ^ w)
    (hlogW : Nat.log 2 (2 * tok.tree.n + 1) ≤ 4 * L)
    (hcap : 2 * ((2 * tok.tree.n + 1 : ℕ) : ℤ) *
      ((B + (paths.length : ℤ) * pathTagMagnitude tag) +
        (R + (paths.length : ℤ) * pathTagMagnitude tag)) < (Num.capacity 4 L : ℤ))
    (hroom : heap + paths.length * pathApplySpace L < 2 ^ w) :
    let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
    let s' := applyPathsFold tok.tree tag paths
    ∃ ret cost out trees' depth' treeTok',
      Runs w p ω (updateGoodApplyPathsBody (opTree 2))
        (startState [root, pathsBase, paths.length, tagPtr, heap] mem pos)
        (.returned ret) out cost ∧
      heap ≤ ret ∧ ret ≤ heap + paths.length * pathApplySpace L ∧
      LctInvWith pathPayload s' trees' tok.free depth' ∧
      PathTreeNumericInv s' trees' (B + (paths.length : ℤ) * pathTagMagnitude tag)
        (R + (paths.length : ℤ) * pathTagMagnitude tag) ∧
      Rtree.rep tok.treeHeap s' treeTok' out.mem ∧
      ZeroFrom out.mem ret ∧
      (∀ a < heap, ¬ Rtree.foot tok.treeHeap tok.treeTok a → out.mem a = mem a) ∧
      (∀ a, Rtree.foot tok.treeHeap treeTok' a →
        Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap ≤ a ∧ a < ret)) ∧
      cost + Rtree.phi tok.treeHeap treeTok' out.mem ≤
        paths.length * (pathTreeBudget LinkCut.PathProg.pathC L tok.tree.n + 45) + 30 +
        Rtree.phi tok.treeHeap tok.treeTok mem := by
  dsimp only
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  obtain ⟨hrootDir, hdetect, _, _, _, _, _, _, _, _, _, hlct, htrep, _, _, _, _, _, _, htags⟩ := hrep
  obtain ⟨hOwn, t1, t2, _⟩ := htags
  have hheapW : heap < 2 ^ w := by omega
  have hrootW : root < 2 ^ w := lt_trans (hbelow root (Or.inl (hOwn root (by rw [show root = root + 0 by omega, t1 0 (by omega)]; decide)))) hheapW
  have hhandleW : tok.handle < 2 ^ w := lt_trans (hbelow tok.handle (Or.inl (hOwn tok.handle (by rw [show tok.handle = tok.handle + 0 by omega, t2 0 (by omega)]; decide)))) hheapW
  have htreeHeapFoot : Rtree.foot tok.treeHeap tok.treeTok tok.treeHeap := by
    refine ⟨le_rfl, ?_⟩
    unfold LinkCut.PathProg.arenaEnd LinkCut.PathProg.arenaNb
    omega
  have htreeW : tok.treeHeap < 2 ^ w :=
    lt_trans (hbelow tok.treeHeap (Or.inr (Or.inl htreeHeapFoot))) hheapW
  have hm0 : mem root = tok.handle := by simpa using hrootDir 0 (by simp)
  have hmT : mem tok.handle = tok.treeHeap := by simpa using hdetect 0 (by simp)
  let s0 := startState [root, pathsBase, paths.length, tagPtr, heap] mem pos
  let s1 : State := { s0 with regs := Function.update s0.regs 5 tok.treeHeap }
  let s2 : State := { s1 with regs := Function.update s1.regs 6 heap }
  let s3 : State := { s2 with regs := Function.update s2.regs 7 0 }
  have r1 : Runs w p ω (.assign 5 (.load (.load (.reg 0)))) s0 .normal s1 4 :=
    runs_assign_iff.mpr ⟨tok.treeHeap, by simp [Expr.eval, s0, startState, hm0, hmT], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 6 (.reg 4)) s1 .normal s2 2 :=
    runs_assign_iff.mpr ⟨heap, by simp [Expr.eval, s1, s0, startState], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 7 (.const 0)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  obtain ⟨out, cLoop, ret, trees', depth', treeTok', hrLoop, hret6, hretLo, hretHi,
      hW', hnum', hrep', hz', hfr', hft', hcLoop⟩ :=
    updateGoodApplyPathsLoop_runs hfmt4 hTreeImpl (by omega) hw2 (by omega) hpathsEnd htagEnd hroom
      paths.length s3 tok.tree tok.trees tok.free tok.depth tok.treeTok B R le_rfl
      (by simp [s3, s2, s1, s0, startState]) (by simp [s3, s2, s1, s0, startState])
      (by simp [s3, s2, s1, s0, startState]) (by simp [s3, s2, s1])
      (by simp [s3, s2]) (by simp [s3, s2]) (by simp [s3])
      htreeW h2nW hlogW hlct hnum hcap htrep
      (fun a ha => by simp [s3, s2]; exact hbelow a (Or.inr (Or.inl ha)))
      hsepTree hends htagAt
      (fun k hk _ => hconn (paths[k]'hk) (List.getElem_mem hk))
      (by simp [s3, s2]; exact hz)
  have hsub0 : paths.length - paths.length = 0 := Nat.sub_self _
  rw [hsub0, List.drop_zero] at hW' hnum' hrep'
  have rRet : Runs w p ω (.ret (.reg 6)) out (.returned ret) out 2 :=
    runs_ret_iff.mpr ⟨ret, by simp [Expr.eval, hret6], rfl, rfl, rfl⟩
  have hrFull : Runs w p ω (updateGoodApplyPathsBody (opTree 2)) s0 (.returned ret) out
      (4 + (2 + ((2 + cLoop + 1) + 2 + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 4, _, r1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 2, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨out, 2 + cLoop + 1, 2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 2, cLoop, r3, hrLoop, rfl⟩), rRet, rfl⟩), rfl⟩), rfl⟩)
  refine ⟨ret, _, out, trees', depth', treeTok', hrFull,
    by simpa [s3, s2] using hretLo, hretHi, hW', hnum', hrep', hz',
    by simpa [s3, s2, s1, s0, startState] using hfr', by simpa [s3, s2] using hft', ?_⟩
  dsimp only [s3, s2, s1, s0, startState] at hcLoop
  omega

end MinCostFlow.MinRatio
