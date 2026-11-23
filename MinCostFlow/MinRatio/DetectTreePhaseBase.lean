module

public import MinCostFlow.MinRatio.SolverRep
public import MinCostFlow.MinRatio.DetectReset
public import MinCostFlow.MinRatio.PathNumericHistory
public import MinCostFlow.MinRatio.DetectOffTreeDrainBase
import WordRAM.Tactic

/-!
# Definitions and helper lemmas for the tree-phase `Detect` loop

Defines `detectTreeRoundSpace`, `detectTreeStepBudget`, `detectTreeFinalBudget`,
`treeReadySet`, `detectTreeStep`, `detectTreePhaseBody`, `TreePhaseInv`, and the
exhausted-branch / numeric-fit / `Finset` helpers used by `DetectTreePhase`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine

/-- Maximum scratch space consumed by one iteration of `detectTreeStep`
(at most three path-tree operations plus one reset `PathEdgeAt` block). -/
@[expose] def detectTreeRoundSpace (L : ℕ) : ℕ :=
  3 * (20 * LinkCut.PathProg.treeLimbs L + 100) + (2 + 4 * L)

/-- Per-ready-edge amortized cost bound for one `detectTreeStep` iteration
(excluding loop control overhead). -/
@[expose] def detectTreeStepBudget (L n : ℕ) : ℕ :=
  3 * pathTreeBudget LinkCut.PathProg.pathC L n + 87 * L + 220

/-- Final exhausted-search cost bound for `detectTreeStep`. -/
@[expose] def detectTreeFinalBudget (L n : ℕ) : ℕ :=
  pathTreeBudget LinkCut.PathProg.pathC L n + 40

/-- Set of edges reported by `algorithm2_detect cfg model` whose internal IDs currently
lie in the link-cut path tree. -/
@[expose] noncomputable def treeReadySet {cfg : Alg2Config} (model : Alg2State cfg) : Finset ℕ :=
  (algorithm2_detect cfg model).1.filter fun e =>
    model.extToInt e ∈ model.chain.toTreeChain.chainTree.E

/-- One iteration of the tree-phase `Detect` loop (`reg 11` is the loop flag). -/
@[expose] def detectTreeStep (opFindReady opPointRead opPointWrite reset : ℕ) : Stmt :=
  .call 12 opFindReady [.reg 6, .reg 4] ;;
  .assign 10 (.load (.reg 4)) ;;
  .assign 4 (.reg 12) ;;
  .cond (.reg 10)
    (.assign 13 (.load (.bin .add (.reg 7) (.reg 10))) ;;
     .assign 14 (.load (.bin .add (.reg 8) (.reg 13))) ;;
     .store (.reg 3) (.reg 14) ;;
     .assign 3 (.bin .add (.reg 3) (.const 1)) ;;
     .call 12 opPointRead [.reg 6, .reg 10, .reg 4] ;;
     .assign 15 (.bin .add (.bin .add (.reg 4) (.const 2)) (.bin .mul (.const 4) (.reg 5))) ;;
     .cond (.bin .lt (.reg 12) (.reg 15)) (.assign 12 (.reg 15)) .nop ;;
     .assign 16 (.load (.bin .add (.reg 9) (.reg 10))) ;;
     .call 17 reset [.reg 4, .reg 16, .reg 5, .reg 12] ;;
     .call 4 opPointWrite [.reg 6, .reg 10, .reg 12, .reg 17])
    (.assign 11 (.const 0))

/-- Full tree-phase reporting loop for `Detect`, exiting `.normal` once no ready tree
edge remains. -/
@[expose] def detectTreePhaseBody (opFindReady opPointRead opPointWrite reset : ℕ) : Stmt :=
  .assign 11 (.const 1) ;;
  .loop (.reg 11) (detectTreeStep opFindReady opPointRead opPointWrite reset)

theorem detectTreePhaseBody_noRand (opFindReady opPointRead opPointWrite reset : ℕ) :
    (detectTreePhaseBody opFindReady opPointRead opPointWrite reset).NoRand := by
  simp [detectTreePhaseBody, detectTreeStep, Stmt.NoRand]

/-- Loop invariant for the tree phase of `Detect`: `cont = 1` while running (with `rem`
ready tree edges remaining) and `cont = 0` after the exhausted search (`rem = 0`). -/
@[expose] def TreePhaseInv {cfg : Alg2Config} {L P m : ℕ} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    (model : Alg2State cfg) (tok : SolverToken cfg L Rcore) (mem₀ : ℕ → ℕ)
    (root base heap₀ : ℕ) (B R : ℤ) (cont rem phi : ℕ) (s : State) : Prop :=
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  ∃ (treeRep : List ℕ) (curHeap : ℕ) (curTree : PathTreeState) (curTrees : List AuxTree)
    (curTreeTok : Rtree.τ),
    s.regs 0 = root ∧ s.regs 1 = base ∧ s.regs 2 = m ∧
    s.regs 3 = base + 1 + treeRep.length ∧
    s.regs 4 = curHeap ∧ s.regs 5 = L ∧
    s.regs 6 = tok.treeHeap ∧ s.regs 7 = tok.names ∧
    s.regs 8 = tok.inverse ∧ s.regs 9 = tok.slotThresholds ∧
    s.regs 11 = cont ∧
    treeRep.Nodup ∧
    treeRep.toFinset ⊆ treeReadySet model ∧
    (treeReadySet model \ treeRep.toFinset).card = rem ∧
    ListAt s.mem (base + 1) treeRep ∧
    heap₀ ≤ curHeap ∧
    curHeap ≤ heap₀ + (treeRep.length + (1 - cont)) * detectTreeRoundSpace L ∧
    ZeroFrom s.mem curHeap ∧
    curTree.n = tok.tree.n ∧
    LctInvWith pathPayload curTree curTrees tok.free tok.depth ∧
    PathTreeNumericInv curTree curTrees B R ∧
    Rtree.rep tok.treeHeap curTree curTreeTok s.mem ∧
    Rtree.phi tok.treeHeap curTreeTok s.mem = phi ∧
    (∀ a, Rtree.foot tok.treeHeap curTreeTok a →
      Rtree.foot tok.treeHeap tok.treeTok a ∨ (heap₀ ≤ a ∧ a < curHeap)) ∧
    (∀ a < heap₀, ¬ Rtree.foot tok.treeHeap tok.treeTok a →
      (a < base + 1 ∨ base + 1 + treeRep.length ≤ a) → s.mem a = mem₀ a) ∧
    (∀ e ∈ model.extG.E,
      let ei := model.extToInt e
      ei ∈ model.chain.toTreeChain.chainTree.E →
      let slot := mem₀ (tok.slots + ei)
      ∃ val : PathEdgeValue, ∃ account : ℤ,
        (slot, some val) ∈ forestPairs pathPayload curTree.splay curTrees ∧
        (val.originalFlow : ℝ) / (2 : ℝ) ^ P = model.flow e ∧
        (account : ℝ) / (2 : ℝ) ^ P = resetReported model.detectAccum treeRep.toFinset e ∧
        val.detector = account - detectorThreshold P cfg.ε (model.extℓ e) ∧
        (val.originalGradient : ℝ) / (2 : ℝ) ^ P = model.extg e ∧
        (val.length : ℝ) / (2 : ℝ) ^ P = model.extℓ e ∧
        (val.forward = true →
          inducedSubPar pathPayload curTree.splay curTrees (vid (model.chain.toTreeChain.chainTree.head ei)) = slot ∧
          inducedSubPar pathPayload curTree.splay curTrees slot = vid (model.chain.toTreeChain.chainTree.tail ei)) ∧
        (val.forward = false →
          inducedSubPar pathPayload curTree.splay curTrees (vid (model.chain.toTreeChain.chainTree.tail ei)) = slot ∧
          inducedSubPar pathPayload curTree.splay curTrees slot = vid (model.chain.toTreeChain.chainTree.head ei))) ∧
    (∀ slot val, isEdgeSlot curTree.n slot →
      (slot, some val) ∈ forestPairs pathPayload curTree.splay curTrees →
      let ei := mem₀ (tok.names + slot)
      let e := model.intToExt ei
      ei < tok.intCap ∧ ei ∈ model.chain.toTreeChain.chainTree.E ∧
      mem₀ (tok.slots + ei) = slot ∧ e ∈ model.extG.E ∧ model.extToInt e = ei) ∧
    TreeEditNamedSlots curTree curTrees model.chain.toTreeChain.chainTree
      (fun f => mem₀ (tok.slots + f)) (fun k => mem₀ (tok.names + k))

/-- `PathTreeNumericInv` implies `pathTreeFits` for `lctExpose` of any active node. -/
theorem pathTreeFits_expose_of_numeric {L : ℕ} {B R : ℤ}
    {s : PathTreeState} {trees : List AuxTree} {free : List ℕ} {d : ℕ → ℕ} {x : ℕ}
    (W : LctInvWith pathPayload s trees free d) (hn : PathTreeNumericInv s trees B R)
    (hcap : 2 * ((2 * s.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hx : pathTreeActive s x) :
    pathTreeFits 4 L (lctExpose pathPayload s x) := by
  obtain ⟨ts, fs, d', WA, hm⟩ := hx
  have he := freeListInv_unique WA.freeListInv W.freeListInv
  subst fs
  have hact := lct_active_mem_of_same_freeList W WA rfl hm
  obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hact
  obtain ⟨us, WE, hnumE⟩ := pathTreeNumericInv_expose W hn ht hxt
  exact hnumE.fits WE hcap

theorem recordWords_le_pathAlloc (L : ℕ) :
    2 + 4 * L ≤ 20 * LinkCut.PathProg.treeLimbs L + 100 := by
  unfold LinkCut.PathProg.treeLimbs; omega

theorem mem_treeReadySet_iff {cfg : Alg2Config} {model : Alg2State cfg} {e : ℕ} :
    e ∈ treeReadySet model ↔
      e ∈ (algorithm2_detect cfg model).1 ∧
      model.extToInt e ∈ model.chain.toTreeChain.chainTree.E := by
  simp [treeReadySet]

/-- Appending a ready tree edge decreases `(treeReadySet model \ treeRep.toFinset).card`
by one. -/
theorem treeReady_snoc {cfg : Alg2Config} {model : Alg2State cfg}
    {treeRep : List ℕ} {e : ℕ}
    (hnd : treeRep.Nodup) (hsub : treeRep.toFinset ⊆ treeReadySet model)
    (heIn : e ∈ treeReadySet model) (heNot : e ∉ treeRep.toFinset) :
    (treeRep ++ [e]).Nodup ∧
    (treeRep ++ [e]).toFinset ⊆ treeReadySet model ∧
    (treeReadySet model \ (treeRep ++ [e]).toFinset).card + 1 =
      (treeReadySet model \ treeRep.toFinset).card := by
  have hnd' : (treeRep ++ [e]).Nodup := List.nodup_append.mpr
    ⟨hnd, List.nodup_singleton _, fun x hx y hy hxy => by
      have hye : y = e := List.mem_singleton.mp hy
      exact heNot (List.mem_toFinset.mpr ((hxy.trans hye) ▸ hx))⟩
  have hsub' : (treeRep ++ [e]).toFinset ⊆ treeReadySet model := by
    rw [List.toFinset_append, List.toFinset_cons, List.toFinset_nil, LawfulSingleton.insert_empty_eq]
    exact Finset.union_subset hsub (Finset.singleton_subset_iff.mpr heIn)
  refine ⟨hnd', hsub', ?_⟩
  rw [Finset.card_sdiff_of_subset hsub', Finset.card_sdiff_of_subset hsub,
    List.toFinset_card_of_nodup hnd', List.toFinset_card_of_nodup hnd]
  have hle := Finset.card_le_card hsub'
  rw [List.toFinset_card_of_nodup hnd', List.length_append, List.length_singleton] at hle
  simp only [List.length_append, List.length_singleton]
  omega

theorem mem_extG_of_mem_detect {cfg : Alg2Config} {model : Alg2State cfg} {e : ℕ}
    (he : e ∈ (algorithm2_detect cfg model).1) : e ∈ model.extG.E := by
  unfold algorithm2_detect at he
  exact (Finset.mem_filter.mp he).1

/-- Any `Nodup` list whose `toFinset` is a subset of `treeReadySet model` has length `≤ m`. -/
theorem treeRep_length_le_m {cfg : Alg2Config} {model : Alg2State cfg} {m : ℕ}
    {xs : List ℕ} (hextM : ∀ e ∈ model.extG.E, e < m)
    (hnd : xs.Nodup) (hsub : xs.toFinset ⊆ treeReadySet model) :
    xs.length ≤ m := by
  have hc : xs.toFinset.card ≤ (Finset.range m).card :=
    Finset.card_le_card (fun x hx => Finset.mem_range.mpr
      (hextM x (mem_extG_of_mem_detect (mem_treeReadySet_iff.mp (hsub hx)).1)))
  rw [List.toFinset_card_of_nodup hnd, Finset.card_range] at hc
  exact hc

/-- Branchless-style `max` update `if reg 12 < reg 15 then reg 12 := reg 15`. -/
theorem detectTreeMax_runs {w a b : ℕ} {p : Program} {ω : ℕ → Bool} {s : State}
    (hr12 : s.regs 12 = a) (hr15 : s.regs 15 = b) (hw1 : 1 < 2 ^ w) :
    ∃ cM, cM ≤ 8 ∧
      Runs w p ω (.cond (.bin .lt (.reg 12) (.reg 15)) (.assign 12 (.reg 15)) .nop)
        s .normal { s with regs := Function.update s.regs 12 (max a b) } cM := by
  by_cases hlt : a < b
  · have hmaxEq : max a b = b := max_eq_right hlt.le
    refine ⟨6, by omega, runs_cond_iff.mpr ⟨1, 2, by
      simp [Expr.eval, BinOp.eval, hr12, hr15, hlt, hw1],
      by simp only [show (1 : ℕ) ≠ 0 by decide, ↓reduceIte]
         exact runs_assign_iff.mpr ⟨b, by simp [Expr.eval, hr15], rfl,
           by simp [hmaxEq], rfl⟩,
      by simp [Expr.size]⟩⟩
  · have hmaxEq : max a b = a := max_eq_left (Nat.le_of_not_lt hlt)
    have hsEq : { s with regs := Function.update s.regs 12 (max a b) } = s := by
      cases s; simp only [State.mk.injEq, true_and, and_true]
      funext r; by_cases hr : r = 12
      · subst hr; simp only [Function.update_self, hmaxEq]; exact hr12.symm
      · simp [Function.update_of_ne hr]
    refine ⟨5, by omega, runs_cond_iff.mpr ⟨0, 1, by
      simp [Expr.eval, BinOp.eval, hr12, hr15, hlt, show 0 < 2 ^ w by omega],
      by simp only [↓reduceIte, hsEq]; exact runs_nop_iff.mpr ⟨rfl, rfl, rfl⟩,
      by simp [Expr.size]⟩⟩

/-- Exhausted-branch (`slot = 0`) closure for `detectTreeStep`. -/
theorem detectTreeStep_exhausted {w m V psi k epsExp drainUnit reset : ℕ}
    {F : MinRatioFormat w} {cfg : Alg2Config} {Rcore : DSRep (SparseCore.Program.SparseCoreOrdAbs cfg.T)}
    {p : Program} {ω : ℕ → Bool} {opTree : ℕ → ℕ}
    {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore} {mem₀ : ℕ → ℕ}
    {root base heap₀ curHeap : ℕ} {B R : ℤ} {rem phi c1 : ℕ}
    {treeRep : List ℕ} {curTree : PathTreeState} {curTrees : List AuxTree}
    {curTreeTok treeTok1 : (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).τ}
    {s s1 s2 s3 st1 : State} {o1 : Outcome}
    (hrep : (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).rep
      root model tok mem₀)
    (hbelow : ∀ a, (solverStateRep cfg F.limbs F.fmt.precision m V psi k epsExp drainUnit Rcore).foot
      root tok a → a < base)
    (heps : 0 < cfg.ε) (hlen : ∀ e ∈ model.extG.E, 0 < model.extℓ e)
    (hbaseHeap : base + 1 + m ≤ heap₀) (hw10 : 10 < 2 ^ w)
    (hs1 : s1 = { regs := Function.update s.regs 12 o1.value, mem := st1.mem, pos := st1.pos })
    (hs2 : s2 = { s1 with regs := Function.update s1.regs 10 (st1.mem curHeap) })
    (hs3 : s3 = { s2 with regs := Function.update s2.regs 4 o1.value })
    (hr0 : s.regs 0 = root) (hr1 : s.regs 1 = base) (hr2 : s.regs 2 = m)
    (hr3 : s.regs 3 = base + 1 + treeRep.length) (hr5 : s.regs 5 = F.limbs)
    (hr6 : s.regs 6 = tok.treeHeap) (hr7 : s.regs 7 = tok.names)
    (hr8 : s.regs 8 = tok.inverse) (hr9 : s.regs 9 = tok.slotThresholds)
    (hnd : treeRep.Nodup) (hsub : treeRep.toFinset ⊆ treeReadySet model)
    (hremEq : (treeReadySet model \ treeRep.toFinset).card = rem)
    (hlist : ListAt s.mem (base + 1) treeRep)
    (hcurLo : heap₀ ≤ curHeap)
    (hcurHi : curHeap ≤ heap₀ + (treeRep.length + (1 - 1)) * detectTreeRoundSpace F.limbs)
    (hcn : curTree.n = tok.tree.n)
    (hlct : LctInvWith pathPayload curTree curTrees tok.free tok.depth)
    (hnum : PathTreeNumericInv curTree curTrees B R)
    (hphiEq : (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).phi
      tok.treeHeap curTreeTok s.mem = phi)
    (hfootCur : ∀ a, (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).foot
      tok.treeHeap curTreeTok a →
      (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
        (heap₀ ≤ a ∧ a < curHeap))
    (htreeAcc : ∀ e ∈ model.extG.E,
      let ei := model.extToInt e
      ei ∈ model.chain.toTreeChain.chainTree.E →
      let slot := mem₀ (tok.slots + ei)
      ∃ val : PathEdgeValue, ∃ account : ℤ,
        (slot, some val) ∈ forestPairs pathPayload curTree.splay curTrees ∧
        (val.originalFlow : ℝ) / (2 : ℝ) ^ F.fmt.precision = model.flow e ∧
        (account : ℝ) / (2 : ℝ) ^ F.fmt.precision =
          resetReported model.detectAccum treeRep.toFinset e ∧
        val.detector = account - detectorThreshold F.fmt.precision cfg.ε (model.extℓ e) ∧
        (val.originalGradient : ℝ) / (2 : ℝ) ^ F.fmt.precision = model.extg e ∧
        (val.length : ℝ) / (2 : ℝ) ^ F.fmt.precision = model.extℓ e ∧
        (val.forward = true →
          inducedSubPar pathPayload curTree.splay curTrees (vid (model.chain.toTreeChain.chainTree.head ei)) = slot ∧
          inducedSubPar pathPayload curTree.splay curTrees slot = vid (model.chain.toTreeChain.chainTree.tail ei)) ∧
        (val.forward = false →
          inducedSubPar pathPayload curTree.splay curTrees (vid (model.chain.toTreeChain.chainTree.tail ei)) = slot ∧
          inducedSubPar pathPayload curTree.splay curTrees slot = vid (model.chain.toTreeChain.chainTree.head ei)))
    (htreeRev : ∀ slot val, isEdgeSlot curTree.n slot →
      (slot, some val) ∈ forestPairs pathPayload curTree.splay curTrees →
      let ei := mem₀ (tok.names + slot)
      let e := model.intToExt ei
      ei < tok.intCap ∧ ei ∈ model.chain.toTreeChain.chainTree.E ∧
      mem₀ (tok.slots + ei) = slot ∧ e ∈ model.extG.E ∧ model.extToInt e = ei)
    (hns : TreeEditNamedSlots curTree curTrees model.chain.toTreeChain.chainTree
      (fun f => mem₀ (tok.slots + f)) (fun k => mem₀ (tok.names + k)))
    (rCall6 : Runs w p ω (.call 12 (opTree 6) [.reg 6, .reg 4]) s .normal s1 (c1 + 3))
    (rLoadSlot : Runs w p ω (.assign 10 (.load (.reg 4))) s1 .normal s2 3)
    (rSetHeap1 : Runs w p ω (.assign 4 (.reg 12)) s2 .normal s3 2)
    (hrep1 : (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).rep
      tok.treeHeap curTree treeTok1 st1.mem)
    (hlo1 : curHeap ≤ o1.value)
    (hhi1' : o1.value ≤ curHeap + (20 * LinkCut.PathProg.treeLimbs F.limbs + 100))
    (hz1 : ZeroFrom st1.mem o1.value)
    (hfr1 : ∀ a < curHeap, ¬ (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).foot
      tok.treeHeap curTreeTok a → st1.mem a = s.mem a)
    (hft1_0 : ∀ a, (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).foot
      tok.treeHeap treeTok1 a →
      (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).foot tok.treeHeap tok.treeTok a ∨
        (heap₀ ≤ a ∧ a < o1.value))
    (hfr1_0 : ∀ a < heap₀, ¬ (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).foot
      tok.treeHeap tok.treeTok a →
      (a < base + 1 ∨ base + 1 + treeRep.length ≤ a) → st1.mem a = mem₀ a)
    (hc1 : c1 + (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).phi
      tok.treeHeap treeTok1 st1.mem ≤
      pathTreeBudget LinkCut.PathProg.pathC F.limbs curTree.n +
        (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).phi
          tok.treeHeap curTreeTok s.mem)
    (hslot0 : st1.mem curHeap = 0) (hnoReady : ¬ ∃ x, pathTreeReady curTree x) :
    ∃ out cost cont' rem' phi',
      Runs w p ω (detectTreeStep (opTree 6) (opTree 4) (opTree 5) reset) s .normal out cost ∧
      TreePhaseInv (P := F.fmt.precision) (m := m) model tok mem₀ root base heap₀ B R
        cont' rem' phi' out ∧
      ((cont' = 1 ∧ 0 < rem ∧ rem' = rem - 1 ∧
          cost + phi' ≤ detectTreeStepBudget F.limbs tok.tree.n + phi) ∨
       (cont' = 0 ∧ rem = 0 ∧ rem' = 0 ∧
          cost + phi' ≤ detectTreeFinalBudget F.limbs tok.tree.n + phi)) := by
  obtain ⟨_, _, _, _, _, _, hextM, _, _, _, _, _, _, hedgeAcc, _, _, _, _, _, _⟩ := hrep
  have hrem0 : rem = 0 := by
    by_contra hnz
    obtain ⟨e, heDiff⟩ := Finset.card_pos.mp (by omega : 0 < (treeReadySet model \ treeRep.toFinset).card)
    obtain ⟨heTR, heNot⟩ := Finset.mem_sdiff.mp heDiff
    obtain ⟨heDet, heInT⟩ := mem_treeReadySet_iff.mp heTR
    have heE : e ∈ model.extG.E := mem_extG_of_mem_detect heDet
    obtain ⟨val, account, hpair, _, hacc, hdet, _, _⟩ := htreeAcc e heE heInT
    have hnonneg : 0 ≤ val.detector :=
      (detect_residual_pending model heE heps (hlen e heE) hacc hdet).mpr
        (Finset.mem_sdiff.mpr ⟨heDet, heNot⟩)
    have hbrT := (hedgeAcc.1 e heE).2.2
    rw [ite_eq_left heInT] at hbrT
    exact hnoReady ⟨mem₀ (tok.slots + model.extToInt e),
      (pathTreeReady_iff_forestPairs hlct _).mpr ⟨hcn.symm ▸ hbrT.2.1, val, hpair, hnonneg⟩⟩
  let s4 : State := { s3 with regs := Function.update s3.regs 11 0 }
  have rSetCont0 : Runs w p ω (.assign 11 (.const 0)) s3 .normal s4 2 :=
    runs_assign_iff.mpr ⟨0, by simp [Expr.eval, show 0 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have rCond : Runs w p ω (.cond (.reg 10)
      (.assign 13 (.load (.bin .add (.reg 7) (.reg 10))) ;;
       .assign 14 (.load (.bin .add (.reg 8) (.reg 13))) ;;
       .store (.reg 3) (.reg 14) ;;
       .assign 3 (.bin .add (.reg 3) (.const 1)) ;;
       .call 12 (opTree 4) [.reg 6, .reg 10, .reg 4] ;;
       .assign 15 (.bin .add (.bin .add (.reg 4) (.const 2)) (.bin .mul (.const 4) (.reg 5))) ;;
       .cond (.bin .lt (.reg 12) (.reg 15)) (.assign 12 (.reg 15)) .nop ;;
       .assign 16 (.load (.bin .add (.reg 9) (.reg 10))) ;;
       .call 17 reset [.reg 4, .reg 16, .reg 5, .reg 12] ;;
       .call 4 (opTree 5) [.reg 6, .reg 10, .reg 12, .reg 17])
      (.assign 11 (.const 0))) s3 .normal s4 4 :=
    runs_cond_iff.mpr ⟨0, 2, by simp [Expr.eval, hs3, hs2, hslot0],
      by simp only [↓reduceIte]; exact rSetCont0, by simp [Expr.size]⟩
  have rStep : Runs w p ω (detectTreeStep (opTree 6) (opTree 4) (opTree 5) reset)
      s .normal s4 (c1 + 15) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, c1 + 3, 11, rCall6,
      runs_seq_iff.mpr (Or.inr ⟨s2, 3, 7, rLoadSlot,
      runs_seq_iff.mpr (Or.inr ⟨s3, 2, 4, rSetHeap1, rCond, rfl⟩), rfl⟩), by omega⟩)
  have hlenM : treeRep.length ≤ m := treeRep_length_le_m hextM hnd hsub
  refine ⟨s4, c1 + 15, 0, 0,
    (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).phi tok.treeHeap treeTok1 st1.mem,
    rStep, ?_, Or.inr ⟨rfl, hrem0, rfl, ?_⟩⟩
  · refine ⟨treeRep, o1.value, curTree, curTrees, treeTok1,
      by simp [s4, hs3, hs2, hs1, hr0], by simp [s4, hs3, hs2, hs1, hr1],
      by simp [s4, hs3, hs2, hs1, hr2], by simp [s4, hs3, hs2, hs1, hr3],
      by simp [s4, hs3, hs2, hs1], by simp [s4, hs3, hs2, hs1, hr5],
      by simp [s4, hs3, hs2, hs1, hr6], by simp [s4, hs3, hs2, hs1, hr7],
      by simp [s4, hs3, hs2, hs1, hr8], by simp [s4, hs3, hs2, hs1, hr9],
      by simp [s4], hnd, hsub, hrem0 ▸ hremEq,
      fun idx hidx => by
        have ha : base + 1 + idx < heap₀ := by omega
        have hnfCur : ¬ (LinkCut.PathProg.pathRep 4 F.limbs LinkCut.PathProg.pathC).foot
            tok.treeHeap curTreeTok (base + 1 + idx) := fun hc => by
          rcases hfootCur _ hc with h0 | ⟨h1, _⟩
          · have := hbelow _ (Or.inr (Or.inl h0)); omega
          · omega
        exact (by simpa [s4, hs3, hs2, hs1] using
          (hfr1 _ (lt_of_lt_of_le ha hcurLo) hnfCur).trans (hlist idx hidx)),
      le_trans hcurLo hlo1, ?_, by simpa [s4, hs3, hs2, hs1] using hz1, hcn, hlct, hnum,
      by simpa [s4, hs3, hs2, hs1] using hrep1, by simp [s4, hs3, hs2, hs1], hft1_0,
      by simpa [s4, hs3, hs2, hs1] using hfr1_0, htreeAcc, htreeRev, hns⟩
    rw [Nat.sub_self, Nat.add_zero] at hcurHi
    change o1.value ≤ heap₀ + (treeRep.length + 1) * detectTreeRoundSpace F.limbs
    rw [Nat.add_mul, one_mul]
    unfold detectTreeRoundSpace at hcurHi ⊢; omega
  · dsimp only [detectTreeFinalBudget]
    rw [hcn, hphiEq] at hc1; omega

/-- Helper: rewriting `resetReported` over `treeReadySet model` on a tree edge gives
`(algorithm2_detect cfg model).2.detectAccum`. -/
theorem resetReported_treeReadySet_eq {cfg : Alg2Config} (model : Alg2State cfg) {e : ℕ}
    (heE : e ∈ model.extG.E) (heInT : model.extToInt e ∈ model.chain.toTreeChain.chainTree.E) :
    resetReported model.detectAccum (treeReadySet model) e =
      (algorithm2_detect cfg model).2.detectAccum e := by
  unfold resetReported algorithm2_detect
  dsimp only
  by_cases hIn : e ∈ (algorithm2_detect cfg model).1
  · have hInTR : e ∈ treeReadySet model := mem_treeReadySet_iff.mpr ⟨hIn, heInT⟩
    simp only [hInTR, ↓reduceIte]
    unfold algorithm2_detect at hIn
    simp only [Finset.mem_filter] at hIn
    simp [hIn.1, hIn.2]
  · have hNotTR : e ∉ treeReadySet model := fun h => hIn (mem_treeReadySet_iff.mp h).1
    simp only [hNotTR, ↓reduceIte]
    unfold algorithm2_detect at hIn
    simp only [Finset.mem_filter, not_and] at hIn
    simp [heE, hIn heE]

/-- Load the Detect header and initialize the output cursor (`base + 1`) and scratch heap
(`base + 1 + m`). Input arguments: `[root, base]`. -/
@[expose] def detectPrefixLoad : Stmt :=
  .assign 10 (.load (.reg 0)) ;;
  .assign 6 (.load (.reg 10)) ;;
  .assign 7 (.load (.bin .add (.reg 10) (.const 1))) ;;
  .assign 8 (.load (.bin .add (.reg 10) (.const 2))) ;;
  .assign 9 (.load (.bin .add (.reg 10) (.const 3))) ;;
  .assign 2 (.load (.bin .add (.reg 10) (.const 4))) ;;
  .assign 5 (.load (.bin .add (.reg 10) (.const 5))) ;;
  .assign 3 (.bin .add (.reg 1) (.const 1)) ;;
  .assign 4 (.bin .add (.reg 3) (.reg 2))

/-- Running the 9-instruction `Detect` prefix takes 47 steps and loads all header fields. -/
theorem detectPrefixLoad_runs
    {w root base pos handle treeHeap names inverse slotThresholds m L : ℕ}
    {p : Program} {ω : ℕ → Bool} {mem : ℕ → ℕ}
    (hh5 : handle + 5 < 2 ^ w) (hbaseM : base + 1 + m < 2 ^ w)
    (hm0 : mem root = handle) (hdet : DetectHeaderAt mem handle treeHeap names inverse
      slotThresholds m L (mem (handle + 6)) (mem (handle + 7))) :
    ∃ mid,
      Runs w p ω detectPrefixLoad (startState [root, base] mem pos) .normal mid 47 ∧
      mid.mem = mem ∧ mid.pos = pos ∧
      mid.regs 0 = root ∧ mid.regs 1 = base ∧ mid.regs 2 = m ∧
      mid.regs 3 = base + 1 ∧ mid.regs 4 = base + 1 + m ∧ mid.regs 5 = L ∧
      mid.regs 6 = treeHeap ∧ mid.regs 7 = names ∧
      mid.regs 8 = inverse ∧ mid.regs 9 = slotThresholds := by
  let s0 := startState [root, base] mem pos
  let s1 := { s0 with regs := Function.update s0.regs 10 handle }
  let s2 := { s1 with regs := Function.update s1.regs 6 treeHeap }
  let s3 := { s2 with regs := Function.update s2.regs 7 names }
  let s4 := { s3 with regs := Function.update s3.regs 8 inverse }
  let s5 := { s4 with regs := Function.update s4.regs 9 slotThresholds }
  let s6 := { s5 with regs := Function.update s5.regs 2 m }
  let s7 := { s6 with regs := Function.update s6.regs 5 L }
  let s8 := { s7 with regs := Function.update s7.regs 3 (base + 1) }
  let s9 := { s8 with regs := Function.update s8.regs 4 (base + 1 + m) }
  have hmT : mem handle = treeHeap := by simpa using hdet 0 (by simp)
  have hmN : mem (handle + 1) = names := by simpa using hdet 1 (by simp)
  have hmI : mem (handle + 2) = inverse := by simpa using hdet 2 (by simp)
  have hmS : mem (handle + 3) = slotThresholds := by simpa using hdet 3 (by simp)
  have hmM : mem (handle + 4) = m := by simpa using hdet 4 (by simp)
  have hmL : mem (handle + 5) = L := by simpa using hdet 5 (by simp)
  have r1 : Runs w p ω (.assign 10 (.load (.reg 0))) s0 .normal s1 3 :=
    runs_assign_iff.mpr ⟨handle, by simp [Expr.eval, s0, startState, hm0], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 6 (.load (.reg 10))) s1 .normal s2 3 :=
    runs_assign_iff.mpr ⟨treeHeap, by simp [Expr.eval, s1, s0, startState, hmT], rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 7 (.load (.bin .add (.reg 10) (.const 1)))) s2 .normal s3 5 :=
    runs_assign_iff.mpr ⟨names, by
      simp [Expr.eval, BinOp.eval, s2, s1, s0, startState, show 1 < 2 ^ w by omega, show handle + 1 < 2 ^ w by omega, hmN],
      rfl, rfl, rfl⟩
  have r4 : Runs w p ω (.assign 8 (.load (.bin .add (.reg 10) (.const 2)))) s3 .normal s4 5 :=
    runs_assign_iff.mpr ⟨inverse, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, s0, startState, show 2 < 2 ^ w by omega, show handle + 2 < 2 ^ w by omega, hmI],
      rfl, rfl, rfl⟩
  have r5 : Runs w p ω (.assign 9 (.load (.bin .add (.reg 10) (.const 3)))) s4 .normal s5 5 :=
    runs_assign_iff.mpr ⟨slotThresholds, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, s1, s0, startState, show 3 < 2 ^ w by omega, show handle + 3 < 2 ^ w by omega, hmS],
      rfl, rfl, rfl⟩
  have r6 : Runs w p ω (.assign 2 (.load (.bin .add (.reg 10) (.const 4)))) s5 .normal s6 5 :=
    runs_assign_iff.mpr ⟨m, by
      simp [Expr.eval, BinOp.eval, s5, s4, s3, s2, s1, s0, startState, show 4 < 2 ^ w by omega, show handle + 4 < 2 ^ w by omega, hmM],
      rfl, rfl, rfl⟩
  have r7 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 10) (.const 5)))) s6 .normal s7 5 :=
    runs_assign_iff.mpr ⟨L, by
      simp [Expr.eval, BinOp.eval, s6, s5, s4, s3, s2, s1, s0, startState, show 5 < 2 ^ w by omega, hh5, hmL],
      rfl, rfl, rfl⟩
  have r8 : Runs w p ω (.assign 3 (.bin .add (.reg 1) (.const 1))) s7 .normal s8 4 :=
    runs_assign_iff.mpr ⟨base + 1, by
      simp [Expr.eval, BinOp.eval, s7, s6, s5, s4, s3, s2, s1, s0, startState,
        show 1 < 2 ^ w by omega, show base + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
  have r9 : Runs w p ω (.assign 4 (.bin .add (.reg 3) (.reg 2))) s8 .normal s9 4 :=
    runs_assign_iff.mpr ⟨base + 1 + m, by
      simp [Expr.eval, BinOp.eval, s8, s7, s6, hbaseM], rfl, rfl, rfl⟩
  refine ⟨s9, ?_, rfl, rfl,
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState],
    by simp [s9, s8, s7, s6, s5, s4, s3, s2, s1, s0, startState],
    by simp [s9, s8, s7, s6], by simp [s9, s8], by simp [s9],
    by simp [s9, s8, s7], by simp [s9, s8, s7, s6, s5, s4, s3, s2],
    by simp [s9, s8, s7, s6, s5, s4, s3], by simp [s9, s8, s7, s6, s5, s4],
    by simp [s9, s8, s7, s6, s5]⟩
  exact runs_seq_iff.mpr (Or.inr ⟨s1, 3, 43, r1,
    runs_seq_iff.mpr (Or.inr ⟨s2, 3, 39, r2,
    runs_seq_iff.mpr (Or.inr ⟨s3, 5, 33, r3,
    runs_seq_iff.mpr (Or.inr ⟨s4, 5, 27, r4,
    runs_seq_iff.mpr (Or.inr ⟨s5, 5, 21, r5,
    runs_seq_iff.mpr (Or.inr ⟨s6, 5, 15, r6,
    runs_seq_iff.mpr (Or.inr ⟨s7, 5, 9, r7,
    runs_seq_iff.mpr (Or.inr ⟨s8, 4, 4, r8, r9, rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩), rfl⟩)

end MinCostFlow.MinRatio
