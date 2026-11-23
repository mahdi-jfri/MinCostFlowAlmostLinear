module

public import MinCostFlow.MinRatio.MinRatioMachineAssembly
public import MinCostFlow.MinRatio.InitIntThresholds
public import MinCostFlow.MinRatio.OrdRebuildSuffix
public import MinCostFlow.MinRatio.SolverLevelCapsInv
import MinCostFlow.LSF.Walks

/-!
# Wired ordered Algorithm 2 initialization: entry body, specs and layout lemmas

The first half of the wired `Init` (`MinRatio/SolverInitWired.lean`): the entry procedure
`solverInitWiredBody`, the concrete initializer contract `OrdInitConcreteSpec`, the ghost
region tags `initSolverTag` of the initial token with their properties
(`initSolverTag_spec`), and layout lemmas.

The wired procedure as a whole:

Composes an ordered concrete deterministic initializer (`OrdInitConcreteSpec`, targeting
`Chain.Ordered.algorithm1_initialize` and `Rcore : DSRep (SparseCoreOrdAbs cfg.T)`) with
`initOverwriteIntThresholdsBody` (which overwrites `table[0..d]` in-place with the exact
integer rebuild thresholds `intRebuildThreshold cfg.P (4 * cfg.P.M₀) j`) into
`solverInitWiredBody`, constructs the initial `SolverToken` with pairwise-disjoint region
tags `SolverTagsAt`, proves `solverStateRep.rep` (including `SolverWireInv` and
`SolverEdgeOrientInv`), `PathTreeNumericInv`, `OffTreeRecInv`, and `MinRatioStateFits`,
and discharges `SolverInitStepSpec`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program IPM.Machine SparseCore.Program

/-- Deterministic wired `Init` entry procedure taking `[graph, g, l, L, P, V, root]` and
returning the final heap pointer after growing the internal tables to `initTargetCap cfg G`:
1. Saves `root` (`reg 6`) into `reg 8`.
2. Calls `initConcreteProc`, storing the concrete heap end in `reg 9`.
3. Calls `overwriteIntThresholdsProc [root]` (`initOverwriteIntThresholdsBody`), overwriting
   `table[0..d]` in-place with `intRebuildThreshold cfg.P (4 * cfg.P.M₀) j` and returning
   `newCap = cfg.P.M₀ + intRebuildThreshold cfg.P (4 * cfg.P.M₀) 0 + 2 * m` in `reg 7`.
4. Runs `growIntTablesFromReg7 copyWords` to grow all six `intCap`-indexed tables to `newCap`
   so the growth branch of `Update` never runs on reached states, and returns `reg 14`. -/
@[expose] def solverInitWiredBody (initConcreteProc overwriteIntThresholdsProc copyWords : ℕ) : Stmt :=
  .assign 8 (.reg 6) ;;
  .call 9 initConcreteProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6] ;;
  .call 7 overwriteIntThresholdsProc [.reg 8] ;;
  .assign 0 (.reg 8) ;;
  .assign 5 (.load (.bin .add (.reg 0) (.const 15))) ;;
  .assign 8 (.reg 9) ;;
  growIntTablesFromReg7 copyWords ;;
  .ret (.reg 14)

theorem solverInitWiredBody_noRand (initConcreteProc overwriteIntThresholdsProc copyWords : ℕ) :
    (solverInitWiredBody initConcreteProc overwriteIntThresholdsProc copyWords).NoRand := by
  simp [solverInitWiredBody, growIntTablesFromReg7_noRand, Stmt.NoRand]

/-- Disjointness and representation invariant for all `C.d` ordered sparse-core levels
(`DSRep (SparseCoreOrdAbs T)` representing `chainLevelOrdAbs chain i`) and the terminal
last-level data structure after ordered Algorithm 2 initialization. -/
@[expose] def OrdInitChainCoresAt {T : SparseCoreRestartTool} {C : ChainParams}
    (Rcore : DSRep (SparseCoreOrdAbs T)) (Rterm : DSRep (ℕ × (ℕ → LSF)))
    (Rtree : DSRep PathTreeState)
    (chain : ChainState T C) (treeHandle levelTable branchTable
      rootBase edgeRecords edgeThresholds slots names slotThresholds m L heap : ℕ)
    (G : MGraph) (recPtr : ℕ → ℕ) (extraStatic : ℕ → Prop)
    (xCore : ℕ → Rcore.τ) (xTerm : Rterm.τ) (xTree : Rtree.τ) (mem : ℕ → ℕ) : Prop :=
  let Ttree := chain.toTreeChain.chainTree
  (∀ i < C.d,
    mem (branchTable + i) = chain.bran i ∧
    Rcore.rep (mem (levelTable + i)) (chainLevelOrdAbs chain i) (xCore i) mem ∧
    (∀ a, Rcore.foot (mem (levelTable + i)) (xCore i) a →
      a < heap ∧
      OutsideInitSlotTables slots names slotThresholds m G.n a ∧
      ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a ∧
      ¬ Rtree.foot treeHandle xTree a ∧
      (∀ j < C.d, j ≠ i → ¬ Rcore.foot (mem (levelTable + j)) (xCore j) a) ∧
      ¬ Rterm.foot (mem (levelTable + C.d)) xTerm a)) ∧
  mem (branchTable + C.d) = chain.lastBran ∧
  Rterm.rep (mem (levelTable + C.d)) (chain.lastK, chain.lastLSFs) xTerm mem ∧
  (∀ a, Rterm.foot (mem (levelTable + C.d)) xTerm a →
    a < heap ∧
    OutsideInitSlotTables slots names slotThresholds m G.n a ∧
    ¬ InitChainStaticAddr rootBase levelTable branchTable edgeRecords edgeThresholds C.d m L G Ttree recPtr extraStatic a ∧
    ¬ Rtree.foot treeHandle xTree a ∧
    (∀ j < C.d, ¬ Rcore.foot (mem (levelTable + j)) (xCore j) a))

/-- Modular contract for the ordered concrete Init body `initConcreteProc` taking
`[graph, gradient, lengths, L, P, V, root]` and returning `finalHeap`.
Builds the root graph, ordered sparse-core levels (`OrdSortedEnds` + `OrdRebuildSuffix`),
terminal last-level structure, Section 6 link-cut path tree, Detect thresholds and initial
`PathEdgeAt` records, and the 16-word `SolverRootDirAt` at `root`. -/
@[expose] def OrdInitConcreteSpec (w L P m V psi k epsExp : ℕ) (cfg : Alg2Config)
    (Rcore : DSRep (SparseCoreOrdAbs cfg.T)) (G : MGraph) (p : Program)
    (initConcreteProc : ℕ) (B_tree : ℤ) : Prop :=
  ∃ body, p.procs[initConcreteProc]? = some body ∧
    ∀ (graph gradient lengths root pos : ℕ) (ω : ℕ → Bool) (mem : ℕ → ℕ),
      let grad₀ := IPM.Machine.readVector mem gradient 4 L P m
      let len₀ := IPM.Machine.readVector mem lengths 4 L P m
      let lenInt := fun e => (Num.intVal mem (lengths + e * L) 4 L).toNat
      let gradInt := fun e => Num.intVal mem (gradient + e * L) 4 L
      let s0 := Chain.Ordered.algorithm2_init cfg G grad₀ len₀
      let chain := s0.chain
      let d := cfg.P.d
      let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
      IPM.Machine.GraphAt mem graph G →
      graph + (IPM.Machine.graphWords G).length ≤ root →
      lengths + G.m * L ≤ root →
      gradient + G.m * L ≤ root →
      (∀ e < m, Num.Valid mem (lengths + e * L) 4 L ∧ 0 < Num.intVal mem (lengths + e * L) 4 L ∧
        Num.Valid mem (gradient + e * L) 4 L) →
      ZeroFrom mem root →
      ∃ (mid : State) (cInit table levelsEnd treeEnd finalHeap vcLast ecLast : ℕ)
        (sFin : PathTreeState) (yTree : Rtree.τ)
        (slotFin nameFin : ℕ → ℕ) (yCore : ℕ → Rcore.τ) (yTerm : ℕ),
        let rootGraph := root + 16 + (L + 1) + 6
        let handle := table + (d + 1)
        let levelTable := handle + 18
        let branchTable := levelTable + (d + 1)
        let freshCounter := levelsEnd + (4 * (d + 1) + 1)
        let forward := freshCounter + 1
        let inverse := forward + m
        let edgeThresholds := inverse + m
        let treeHeap := edgeThresholds + m
        let slots := treeEnd
        let names := treeEnd + m
        let slotThresholds := treeEnd + m + 2 * G.n
        let edgeRecords := treeEnd + m + 2 * G.n + 2 * G.n
        let offReadyList := treeEnd + m + 2 * G.n + 2 * G.n + m
        let inOffReady := treeEnd + m + 2 * G.n + 2 * G.n + m + m
        let threshHeap := treeEnd + m + 2 * G.n + 2 * G.n + m + m + m
        let afterThresh := threshHeap + 3 * L + m * initEdgeRecordSpace L
        let thPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L
        let recPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L
        let extraStatic := fun a => a < branchTable + (d + 1) ∨
          (levelsEnd ≤ a ∧ a < treeHeap) ∨ (edgeRecords + m ≤ a ∧ a < afterThresh)
        Runs w p ω body (startState [graph, gradient, lengths, L, P, V, root] mem pos)
          (.returned finalHeap) mid cInit ∧
        SolverRootDirAt mid.mem root handle table levelsEnd forward inverse freshCounter
          slots names slotThresholds edgeThresholds edgeRecords 0 offReadyList inOffReady rootGraph m ∧
        DetectHeaderAt mid.mem handle treeHeap names inverse slotThresholds m L
          (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
        MinRatioNumericHeaderAt mid.mem handle L P (20 * (4 * L + 8) + 100) (20 * (4 * L + 8) + 100) ∧
        SolverChainHeaderAt mid.mem handle m V d cfg.P.k psi (root + 16) k epsExp
          (Expander.chosenL (cfg.P.M₀ ^ 2)) ∧
        FreshTablesAt mid.mem forward inverse freshCounter m m id id m ∧
        (∀ a, levelsEnd ≤ a → a < levelsEnd + (4 * (d + 1) + 1) → mid.mem a = 0) ∧
        (∀ e < m, mid.mem (inOffReady + e) = 0) ∧
        (∀ e < m,
          mid.mem (edgeThresholds + e) = thPtr e ∧
          mid.mem (edgeRecords + e) = recPtr e ∧
          PathIntAt mid.mem (thPtr e) 4 L (detectorThreshold P cfg.ε ((lenInt e : ℝ) / (2 : ℝ) ^ P)) ∧
          PathEdgeAt mid.mem (recPtr e) 4 L (some (initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e)))) ∧
        InitPathTreeInv Rtree treeHeap G chain.toTreeChain.chainTree
          (fun e => initialPathEdgeValue P cfg.ε (gradInt e) (lenInt e)) B_tree
          slots names slotThresholds m thPtr chain.toTreeChain.chainTree.E
          sFin yTree slotFin nameFin finalHeap mid.mem ∧
        ZeroFrom mid.mem finalHeap ∧
        root ≤ finalHeap ∧
        (∀ a < root, mid.mem a = mem a) ∧
        DynGraphAt mid.mem rootGraph G.n m G ∧
        rootGraph + dynGraphSize G.n m ≤ table ∧
        branchTable + (d + 1) ≤ levelsEnd ∧
        treeHeap ≤ treeEnd ∧
        afterThresh ≤ finalHeap ∧
        finalHeap < 2 ^ w ∧
        (∀ a, Rtree.foot treeHeap yTree a →
          OutsideInitSlotTables slots names slotThresholds m G.n a ∧
          ¬ InitChainStaticAddr rootGraph levelTable branchTable edgeRecords edgeThresholds
              d m L G chain.toTreeChain.chainTree recPtr extraStatic a) ∧
        OrdInitChainCoresAt Rcore
          (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (chain.G d).E)
          Rtree chain treeHeap levelTable branchTable rootGraph edgeRecords edgeThresholds
          slots names slotThresholds m L finalHeap G recPtr extraStatic yCore yTerm yTree mid.mem

/-- Uniqueness of the `PathEdgeValue` stored at a `PathEdgeAt` block. -/
theorem initPathEdgeAt_unique {mem : ℕ → ℕ} {a h L : ℕ} {v₁ v₂ : PathEdgeValue}
    (h1 : PathEdgeAt mem a h L (some v₁)) (h2 : PathEdgeAt mem a h L (some v₂)) :
    v₁ = v₂ := by
  obtain ⟨_, hf1, hg1, hl1, hfl1, hd1⟩ := h1
  obtain ⟨_, hf2, hg2, hl2, hfl2, hd2⟩ := h2
  have hfwd : v₁.forward = v₂.forward := by
    cases hb1 : v₁.forward <;> cases hb2 : v₂.forward
    · rfl
    · simp [hb1, hb2] at hf1 hf2; omega
    · simp [hb1, hb2] at hf1 hf2; omega
    · rfl
  have hgrad : v₁.gradient = v₂.gradient := hg1.2.symm.trans hg2.2
  have hlen : v₁.length = v₂.length := hl1.2.symm.trans hl2.2
  have hflow : v₁.flow = v₂.flow := hfl1.2.symm.trans hfl2.2
  have hdet : v₁.detector = v₂.detector := hd1.2.symm.trans hd2.2
  cases v₁; cases v₂; simp_all

/-- Permutation between the node-id projection of `forestPairs` and `trees.flatMap AuxTree.toList`. -/
theorem init_forestPairs_map_fst_perm
    (s : SplayState (Option PathEdgeValue) PathSummary PathTag) (trees : List AuxTree) :
    ((forestPairs pathPayload s trees).map Prod.fst).Perm (trees.flatMap AuxTree.toList) := by
  have hev : ∀ (t : AuxTree) (b : Bool),
      (AuxTree.evalInorder (fun id => (s.nodes id).rev) t b).Perm t.toList := by
    intro t
    induction t with
    | leaf => intro _; simp [AuxTree.evalInorder, AuxTree.toList]
    | node x l r ihl ihr =>
      intro b
      cases b
      · simp only [AuxTree.evalInorder, AuxTree.toList, List.append_assoc, List.singleton_append]
        exact (ihl _).append (List.Perm.cons x (ihr _))
      · simp only [AuxTree.evalInorder, AuxTree.toList, List.append_assoc, List.singleton_append]
        have hp := (ihr (!(s.nodes x).rev)).append (List.Perm.cons x (ihl (!(s.nodes x).rev)))
        exact hp.trans (List.perm_middle.trans
          ((List.Perm.cons x List.perm_append_comm).trans List.perm_middle.symm))
  induction trees with
  | nil => simp [forestPairs]
  | cons t rest ih =>
    simp only [forestPairs, List.flatMap_cons, List.map_append]
    have ht : ((SplayState.evalPairs pathPayload s t false pathPayload.idTag).map Prod.fst).Perm t.toList := by
      rw [SplayState.evalPairs_map_fst]; exact hev t false
    exact ht.append ih

/-- Uniqueness of the second component for a given node id in `forestPairs`. -/
theorem init_forestPairs_snd_unique
    {s : SplayState (Option PathEdgeValue) PathSummary PathTag}
    {trees : List AuxTree} (hnd : (trees.flatMap AuxTree.toList).Nodup)
    {a : ℕ} {b₁ b₂ : Option PathEdgeValue}
    (h1 : (a, b₁) ∈ forestPairs pathPayload s trees)
    (h2 : (a, b₂) ∈ forestPairs pathPayload s trees) : b₁ = b₂ := by
  have hndP : ((forestPairs pathPayload s trees).map Prod.fst).Nodup :=
    (init_forestPairs_map_fst_perm s trees).nodup_iff.mpr hnd
  have hmem : ∀ {l : List (ℕ × Option PathEdgeValue)}, (l.map Prod.fst).Nodup →
      ∀ {x : ℕ} {y₁ y₂ : Option PathEdgeValue}, (x, y₁) ∈ l → (x, y₂) ∈ l → y₁ = y₂ := by
    intro l hndl
    induction l with
    | nil => intro _ _ _ h; cases h
    | cons p rest ih =>
      intro x y₁ y₂ hp1 hp2
      rw [List.map_cons, List.nodup_cons] at hndl
      rcases List.mem_cons.mp hp1 with rfl | hp1' <;> rcases List.mem_cons.mp hp2 with h2' | hp2'
      · exact (Prod.mk.inj h2').2.symm
      · exfalso; exact hndl.1 (List.mem_map.mpr ⟨(x, y₂), hp2', rfl⟩)
      · subst h2'; exfalso; exact hndl.1 (List.mem_map.mpr ⟨(x, y₁), hp1', rfl⟩)
      · exact ih hndl.2 hp1' hp2'
  exact hmem hndP h1 h2

theorem init_thPtr_recPtr_disjoint {threshHeap L e e' j j' : ℕ}
    (hj : j < L) (hj' : j' < 2 + 4 * L) :
    threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + j ≠
      threshHeap + 3 * L + e' * initEdgeRecordSpace L + Num.fixedDivideSpace L + L + j' := by
  unfold initEdgeRecordSpace
  rcases lt_trichotomy e e' with hlt | rfl | hgt
  · have hstep : (e + 1) * (Num.fixedDivideSpace L + 5 * L + 2) ≤
        e' * (Num.fixedDivideSpace L + 5 * L + 2) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hlt)
    rw [Nat.succ_mul] at hstep; omega
  · omega
  · have hstep : (e' + 1) * (Num.fixedDivideSpace L + 5 * L + 2) ≤
        e * (Num.fixedDivideSpace L + 5 * L + 2) :=
      Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hgt)
    rw [Nat.succ_mul] at hstep; omega

theorem init_thPtr_bounds {threshHeap L m e j : ℕ} (he : e < m) (hj : j < L) :
    threshHeap ≤ threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + j ∧
    threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + j <
      threshHeap + 3 * L + m * initEdgeRecordSpace L := by
  have hm : (e + 1) * initEdgeRecordSpace L ≤ m * initEdgeRecordSpace L :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at hm
  unfold initEdgeRecordSpace at hm ⊢
  omega

theorem init_recPtr_bounds {threshHeap L m e j : ℕ} (he : e < m) (hj : j < 2 + 4 * L) :
    threshHeap ≤ threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L + j ∧
    threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L + j <
      threshHeap + 3 * L + m * initEdgeRecordSpace L := by
  have hm : (e + 1) * initEdgeRecordSpace L ≤ m * initEdgeRecordSpace L :=
    Nat.mul_le_mul_right _ (Nat.succ_le_of_lt he)
  rw [Nat.succ_mul] at hm
  unfold initEdgeRecordSpace at hm ⊢
  omega

/-- Ghost region-tag function for the initial `SolverToken` constructed by
`solverInitWiredBody`. Every region (`1..20`, `21 + i` for `i < d`, and `21 + d`, `22 + d`,
`23 + d` for level metadata) gets a distinct nonzero tag, and every tagged address lies in
`[root, finalHeap)`. -/
@[expose] noncomputable def initSolverTag {cfg : Alg2Config} {L : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (root rootGraph len0Buf table levelsEnd treeEnd m n eCap vcLast ecLast : ℕ)
    (Glast : MGraph) (yTree : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ)
    (yTerm : ℕ) (coreHandle : ℕ → ℕ) (yCore : ℕ → Rcore.τ) (termHandle : ℕ)
    (metaL metaG : ℕ → ℕ) (a : ℕ) : ℕ :=
  open Classical in
  let d := cfg.P.d
  let n0Cell := solverN0Addr table d
  let levelMeta := solverLevelMetaAddr table d
  let selectHeap := solverSelectHeapAddr table d
  let handle := solverHandleAddr table d
  let levelTable := handle + 18
  let branchTable := levelTable + (d + 1)
  let freshCounter := levelsEnd + (4 * (d + 1) + 1)
  let forward := freshCounter + 1
  let inverse := forward + m
  let edgeThresholds := inverse + m
  let treeHeap := edgeThresholds + m
  let slots := treeEnd
  let names := treeEnd + m
  let slotThresholds := treeEnd + m + 2 * n
  let edgeRecords := treeEnd + m + 2 * n + 2 * n
  let offReadyList := treeEnd + m + 2 * n + 2 * n + m
  let inOffReady := treeEnd + m + 2 * n + 2 * n + m + m
  let threshHeap := treeEnd + m + 2 * n + 2 * n + m + m + m
  let thPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L
  let recPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let Rterm := LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L 0 Glast.E
  if root ≤ a ∧ a < root + 16 then 1
  else if rootGraph ≤ a ∧ a < rootGraph + dynGraphSize n eCap then 20
  else if len0Buf ≤ a ∧ a < table then 23 + d
  else if table ≤ a ∧ a < n0Cell then 3
  else if (n0Cell ≤ a ∧ a < levelMeta) ∨ (selectHeap ≤ a ∧ a < handle) then 21 + d
  else if levelMeta ≤ a ∧ a < selectHeap then 22 + d
  else if handle ≤ a ∧ a < levelTable then 2
  else if levelTable ≤ a ∧ a < branchTable + (d + 1) then 4
  else if ∃ j, 1 ≤ j ∧ j < d ∧
      ((metaL j ≤ a ∧ a < metaL j + eCap * L) ∨
       (metaG j ≤ a ∧ a < metaG j + dynGraphSize n eCap)) then 23 + d
  else if levelsEnd ≤ a ∧ a < freshCounter then 5
  else if a = freshCounter then 6
  else if forward ≤ a ∧ a < inverse then 7
  else if inverse ≤ a ∧ a < edgeThresholds then 8
  else if edgeThresholds ≤ a ∧ a < treeHeap then 12
  else if slots ≤ a ∧ a < names then 9
  else if names ≤ a ∧ a < slotThresholds then 10
  else if slotThresholds ≤ a ∧ a < edgeRecords then 11
  else if edgeRecords ≤ a ∧ a < offReadyList then 13
  else if offReadyList ≤ a ∧ a < inOffReady then 14
  else if inOffReady ≤ a ∧ a < threshHeap then 15
  else if ∃ e < m, thPtr e ≤ a ∧ a < thPtr e + L then 17
  else if ∃ e < m, recPtr e ≤ a ∧ a < recPtr e + (2 + 4 * L) then 18
  else if Rtree.foot treeHeap yTree a then 16
  else if Rterm.foot termHandle yTerm a then 19
  else if h : ∃ i < d, Rcore.foot (coreHandle i) (yCore i) a then 21 + Classical.choose h
  else 0

/-- Build `SolverTagsAt`, `SolverLevelCapsInv`, and footprint bounds `[root, finalHeap)` for
`initSolverTag` directly from the monotonic layout and `OrdInitChainCoresAt` / `Rtree.foot`
disjointness. -/
theorem initSolverTag_spec {cfg : Alg2Config} {L P m eCap V psi k epsExp : ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {root rootGraph len0Buf table levelsEnd treeEnd finalHeap vcLast ecLast : ℕ}
    {G : MGraph} {sFin : PathTreeState}
    {yTree : (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).τ}
    {yCore : ℕ → Rcore.τ} {yTerm : ℕ} {mem : ℕ → ℕ}
    {model : Alg2State cfg}
    (hExtG : model.extG = G) (hExtToInt : model.extToInt = id)
    (hGE : G.E = Finset.range m) (hsn : sFin.n = G.n)
    (hmPos : 0 < m) (hmLeECap : m ≤ eCap) (hLpos : 0 < L)
    (hroot16Le : root + 16 ≤ rootGraph)
    (hrootGLe : rootGraph + dynGraphSize G.n eCap ≤ len0Buf)
    (hlen0Eq : len0Buf + eCap * L = table)
    (hlevGe : solverHandleAddr table cfg.P.d + 18 + (cfg.P.d + 1) + (cfg.P.d + 1) ≤ levelsEnd)
    (htreeLe : levelsEnd + (4 * (cfg.P.d + 1) + 1) + 1 + m + m + m ≤ treeEnd)
    (hafterLe : treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + m * initEdgeRecordSpace L ≤ finalHeap)
    (hDG0 : DynGraphAt mem rootGraph G.n eCap (model.chain.G 0))
    (hMeta :
      let d := cfg.P.d
      let n0Cell := solverN0Addr table d
      let lvlMTable := solverLvlMAddr table d
      let levelMeta := solverLevelMetaAddr table d
      let levelTable := solverHandleAddr table d + 18
      let branchTable := levelTable + (d + 1)
      mem n0Cell = model.chain.N₀ ∧
      (∀ j < d, mem (lvlMTable + j) = model.chain.lvlM j) ∧
      (∀ j < d, branchTable + (d + 1) ≤ mem (levelTable + j) ∧ mem (levelTable + j) ≤ levelsEnd) ∧
      mem (levelMeta + 0) = len0Buf ∧
      mem (levelMeta + d + 0) = rootGraph ∧
      EdgeValuesAt mem len0Buf 4 L P (model.chain.G 0).E
        (model.chain.toTreeChain.chainLen model.chain.ℓ 0) ∧
      (∀ j, 1 ≤ j → j < d →
        DynGraphAt mem (mem (levelMeta + d + j)) G.n eCap (model.chain.G j) ∧
        EdgeValuesAt mem (mem (levelMeta + j)) 4 L P (model.chain.G j).E
          (model.chain.toTreeChain.chainLen model.chain.ℓ j) ∧
        branchTable + (d + 1) ≤ mem (levelMeta + j) ∧
        mem (levelMeta + j) + eCap * L ≤ levelsEnd ∧
        branchTable + (d + 1) ≤ mem (levelMeta + d + j) ∧
        mem (levelMeta + d + j) + dynGraphSize G.n eCap ≤ levelsEnd))
    (hptrAt : ∀ e < m,
      mem (levelsEnd + (4 * (cfg.P.d + 1) + 1) + 1 + m + m + e) =
        treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L ∧
      mem (treeEnd + m + 2 * G.n + 2 * G.n + e) =
        treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L)
    (hfootTreeLt : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot
      (levelsEnd + (4 * (cfg.P.d + 1) + 1) + 1 + m + m + m) yTree a → a < finalHeap)
    (htreeDisj : ∀ a, (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC).foot
      (levelsEnd + (4 * (cfg.P.d + 1) + 1) + 1 + m + m + m) yTree a →
      OutsideInitSlotTables treeEnd (treeEnd + m) (treeEnd + m + 2 * G.n) m G.n a ∧
      ¬ InitChainStaticAddr rootGraph
          (solverHandleAddr table cfg.P.d + 18) (solverHandleAddr table cfg.P.d + 18 + (cfg.P.d + 1))
          (treeEnd + m + 2 * G.n + 2 * G.n) (levelsEnd + (4 * (cfg.P.d + 1) + 1) + 1 + m + m)
          cfg.P.d m L G model.chain.toTreeChain.chainTree
          (fun e => treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L)
          (fun a => a < solverHandleAddr table cfg.P.d + 18 + (cfg.P.d + 1) + (cfg.P.d + 1) ∨
            (∃ j, 1 ≤ j ∧ j < cfg.P.d ∧
              ((mem (solverLevelMetaAddr table cfg.P.d + j) ≤ a ∧
                a < mem (solverLevelMetaAddr table cfg.P.d + j) + eCap * L) ∨
               (mem (solverLevelMetaAddr table cfg.P.d + cfg.P.d + j) ≤ a ∧
                a < mem (solverLevelMetaAddr table cfg.P.d + cfg.P.d + j) + dynGraphSize G.n eCap))) ∨
            (levelsEnd ≤ a ∧ a < levelsEnd + (4 * (cfg.P.d + 1) + 1) + 1 + m + m + m) ∨
            (treeEnd + m + 2 * G.n + 2 * G.n + m ≤ a ∧
              a < treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + m * initEdgeRecordSpace L)) a)
    (hcoresAt : OrdInitChainCoresAt Rcore
      (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L P (model.chain.G cfg.P.d).E)
      (LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC)
      model.chain (levelsEnd + (4 * (cfg.P.d + 1) + 1) + 1 + m + m + m)
      (solverHandleAddr table cfg.P.d + 18) (solverHandleAddr table cfg.P.d + 18 + (cfg.P.d + 1))
      rootGraph (treeEnd + m + 2 * G.n + 2 * G.n)
      (levelsEnd + (4 * (cfg.P.d + 1) + 1) + 1 + m + m)
      treeEnd (treeEnd + m) (treeEnd + m + 2 * G.n) m L finalHeap G
      (fun e => treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L)
      (fun a => a < solverHandleAddr table cfg.P.d + 18 + (cfg.P.d + 1) + (cfg.P.d + 1) ∨
        (∃ j, 1 ≤ j ∧ j < cfg.P.d ∧
          ((mem (solverLevelMetaAddr table cfg.P.d + j) ≤ a ∧
            a < mem (solverLevelMetaAddr table cfg.P.d + j) + eCap * L) ∨
           (mem (solverLevelMetaAddr table cfg.P.d + cfg.P.d + j) ≤ a ∧
            a < mem (solverLevelMetaAddr table cfg.P.d + cfg.P.d + j) + dynGraphSize G.n eCap))) ∨
        (levelsEnd ≤ a ∧ a < levelsEnd + (4 * (cfg.P.d + 1) + 1) + 1 + m + m + m) ∨
        (treeEnd + m + 2 * G.n + 2 * G.n + m ≤ a ∧
          a < treeEnd + m + 2 * G.n + 2 * G.n + m + m + m + 3 * L + m * initEdgeRecordSpace L))
      yCore yTerm yTree mem) :
    let d := cfg.P.d
    let levelMeta := solverLevelMetaAddr table d
    let handle := solverHandleAddr table d
    let levelTable := handle + 18
    let freshCounter := levelsEnd + (4 * (d + 1) + 1)
    let forward := freshCounter + 1
    let inverse := forward + m
    let edgeThresholds := inverse + m
    let treeHeap := edgeThresholds + m
    let slots := treeEnd
    let names := treeEnd + m
    let slotThresholds := treeEnd + m + 2 * G.n
    let edgeRecords := treeEnd + m + 2 * G.n + 2 * G.n
    let offReadyList := treeEnd + m + 2 * G.n + 2 * G.n + m
    let inOffReady := treeEnd + m + 2 * G.n + 2 * G.n + m + m
    let tagFn := initSolverTag (cfg := cfg) (L := L) (Rcore := Rcore)
      root rootGraph len0Buf table levelsEnd treeEnd m G.n eCap vcLast ecLast (model.chain.G d) yTree yTerm
      (fun i => mem (levelTable + i)) yCore (mem (levelTable + d))
      (fun j => mem (levelMeta + j)) (fun j => mem (levelMeta + d + j))
    let tok : SolverToken cfg L Rcore :=
      { handle := handle, table := table, levelsEnd := levelsEnd,
        forward := forward, inverse := inverse, freshCounter := freshCounter,
        slots := slots, names := names, slotThresholds := slotThresholds,
        edgeThresholds := edgeThresholds, edgeRecords := edgeRecords,
        offReadyCount := 0, offReadyList := offReadyList, inOffReady := inOffReady,
        rootGraph := rootGraph, rootECap := eCap, intCap := m, treeHeap := treeHeap,
        searchSpace := 20 * (4 * L + 8) + 100, readSpace := 20 * (4 * L + 8) + 100,
        alphaPtr := root + 16, tree := sFin, trees := [], free := [], depth := fun _ => 0,
        treeTok := yTree, coreHandle := fun i => mem (levelTable + i), coreTok := yCore,
        termHandle := mem (levelTable + d), vcLast := vcLast, ecLast := ecLast, termTok := yTerm,
        owned := fun a => tagFn a ≠ 0 ∨ (∃ j < d, a = mem (levelTable + j)), tag := tagFn }
    SolverTagsAt root m model tok mem ∧
    SolverLevelCapsInv P V G.n eCap model tok mem ∧
    (∀ a, (solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore).foot root tok a →
      root ≤ a ∧ a < finalHeap) := by
  intro d levelMeta handle levelTable freshCounter forward inverse edgeThresholds
    treeHeap slots names slotThresholds edgeRecords offReadyList inOffReady tagFn tok
  let n0Cell := solverN0Addr table d
  let lvlMTable := solverLvlMAddr table d
  let selectHeap := solverSelectHeapAddr table d
  let branchTable := levelTable + (d + 1)
  let threshHeap := treeEnd + m + 2 * G.n + 2 * G.n + m + m + m
  let afterThresh := threshHeap + 3 * L + m * initEdgeRecordSpace L
  let thPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L
  let recPtr := fun e => threshHeap + 3 * L + e * initEdgeRecordSpace L + Num.fixedDivideSpace L + L
  let Rtree := LinkCut.PathProg.pathRep 4 L LinkCut.PathProg.pathC
  let metaL := fun j => mem (levelMeta + j)
  let metaG := fun j => mem (levelMeta + d + j)
  let metaStatic := fun a => ∃ j, 1 ≤ j ∧ j < d ∧
    ((metaL j ≤ a ∧ a < metaL j + eCap * L) ∨ (metaG j ≤ a ∧ a < metaG j + dynGraphSize G.n eCap))
  let extraStatic := fun a => a < branchTable + (d + 1) ∨ metaStatic a ∨
    (levelsEnd ≤ a ∧ a < treeHeap) ∨ (edgeRecords + m ≤ a ∧ a < afterThresh)
  obtain ⟨hMono1, hMono2, hMono3, hMono4, hMono5, hMono6, hMono7, hMono7b, hMono8, hMono9, hMono10,
      hMono11, hMono12, hMono13, hMono14, hMono15, hMono16, hMono17, hMono18, hMono19, hMono20,
      hMono21, hMono22, hMono23, hMono24⟩ :
      (root + 16 ≤ rootGraph) ∧ (rootGraph + dynGraphSize G.n eCap ≤ len0Buf) ∧
      (len0Buf + eCap * L = table) ∧ (table + (d + 1) = n0Cell) ∧ (n0Cell + 1 = lvlMTable) ∧
      (lvlMTable + d = levelMeta) ∧ (levelMeta + 2 * d = selectHeap) ∧ (selectHeap + 2 = handle) ∧
      (handle + 18 = levelTable) ∧
      (levelTable + (d + 1) = branchTable) ∧ (branchTable + (d + 1) ≤ levelsEnd) ∧
      (levelsEnd + (4 * (d + 1) + 1) = freshCounter) ∧ (freshCounter + 1 = forward) ∧
      (forward + m = inverse) ∧ (inverse + m = edgeThresholds) ∧ (edgeThresholds + m = treeHeap) ∧
      (treeHeap ≤ slots) ∧ (slots + m = names) ∧ (names + 2 * G.n = slotThresholds) ∧
      (slotThresholds + 2 * G.n = edgeRecords) ∧ (edgeRecords + m = offReadyList) ∧
      (offReadyList + m = inOffReady) ∧ (inOffReady + m = threshHeap) ∧
      (threshHeap ≤ afterThresh) ∧ (afterThresh ≤ finalHeap) :=
    ⟨hroot16Le, hrootGLe, hlen0Eq, rfl, rfl, rfl, rfl,
      by dsimp only [selectHeap, handle]; unfold solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr; omega,
      rfl, rfl, hlevGe, rfl, rfl, rfl, rfl, rfl, htreeLe, rfl, rfl, rfl, rfl, rfl, rfl, by omega, hafterLe⟩
  obtain ⟨hN0Val, hMTab, hCoreBds, hMetaL0, hMetaG0, hLen0, hMetaLvls⟩ := hMeta
  simp only [Nat.add_zero] at hMetaL0 hMetaG0
  have hMetaGe (a : ℕ) (hm : metaStatic a) : branchTable + (d + 1) ≤ a ∧ a < levelsEnd := by
    rcases hm with ⟨j, hj1, hjLt, ⟨h1, h2⟩ | ⟨h1, h2⟩⟩
    · obtain ⟨_, _, hlo, hhi, _, _⟩ := hMetaLvls j hj1 hjLt
      dsimp only [metaL, levelMeta, branchTable, levelTable, handle, d] at h1 h2 ⊢; omega
    · obtain ⟨_, _, _, _, hlo, hhi⟩ := hMetaLvls j hj1 hjLt
      dsimp only [metaG, levelMeta, branchTable, levelTable, handle, d] at h1 h2 ⊢; omega
  have hnotMeta_of_ge (a : ℕ) (ha : levelsEnd ≤ a) : ¬ metaStatic a := fun hm =>
    by have := (hMetaGe a hm).2; omega
  have hnot_pre (a : ℕ)
      (hout : OutsideInitSlotTables slots names slotThresholds m G.n a)
      (hnotSt : ¬ InitChainStaticAddr rootGraph levelTable branchTable edgeRecords edgeThresholds
        d m L G model.chain.toTreeChain.chainTree recPtr extraStatic a) :
      ¬ (root ≤ a ∧ a < root + 16) ∧ ¬ (rootGraph ≤ a ∧ a < rootGraph + dynGraphSize G.n eCap) ∧
      ¬ (len0Buf ≤ a ∧ a < table) ∧ ¬ (table ≤ a ∧ a < n0Cell) ∧
      ¬ ((n0Cell ≤ a ∧ a < levelMeta) ∨ (selectHeap ≤ a ∧ a < handle)) ∧
      ¬ (levelMeta ≤ a ∧ a < selectHeap) ∧
      ¬ (handle ≤ a ∧ a < levelTable) ∧ ¬ (levelTable ≤ a ∧ a < branchTable + (d + 1)) ∧
      ¬ metaStatic a ∧ ¬ (levelsEnd ≤ a ∧ a < freshCounter) ∧
      ¬ (a = freshCounter) ∧ ¬ (forward ≤ a ∧ a < inverse) ∧
      ¬ (inverse ≤ a ∧ a < edgeThresholds) ∧ ¬ (edgeThresholds ≤ a ∧ a < treeHeap) ∧
      ¬ (slots ≤ a ∧ a < names) ∧ ¬ (names ≤ a ∧ a < slotThresholds) ∧
      ¬ (slotThresholds ≤ a ∧ a < edgeRecords) ∧ ¬ (edgeRecords ≤ a ∧ a < offReadyList) ∧
      ¬ (offReadyList ≤ a ∧ a < inOffReady) ∧ ¬ (inOffReady ≤ a ∧ a < threshHeap) ∧
      ¬ (∃ e < m, thPtr e ≤ a ∧ a < thPtr e + L) ∧
      ¬ (∃ e < m, recPtr e ≤ a ∧ a < recPtr e + (2 + 4 * L)) ∧ root ≤ a := by
    have hgeBr : branchTable + (d + 1) ≤ a := by
      by_contra h; exact hnotSt (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Nat.lt_of_not_ge h))))))))
    have hnotMs : ¬ metaStatic a :=
      fun h => hnotSt (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))))
    have hnotLv : ¬ (levelsEnd ≤ a ∧ a < treeHeap) :=
      fun h => hnotSt (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))))
    have hnotEr : ¬ (edgeRecords ≤ a ∧ a < edgeRecords + m) :=
      fun h => hnotSt (Or.inr (Or.inr (Or.inr (Or.inl h))))
    have hnotAfter : ¬ (edgeRecords + m ≤ a ∧ a < afterThresh) :=
      fun h => hnotSt (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))))
    refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, hnotMs,
      fun h => hnotLv ⟨h.1, by omega⟩, fun h => hnotLv ⟨by omega, by omega⟩,
      fun h => hnotLv ⟨by omega, by omega⟩, fun h => hnotLv ⟨by omega, by omega⟩,
      fun h => hnotLv ⟨by omega, h.2⟩,
      fun h => hout.1.elim (by omega) (by omega),
      fun h => hout.2.1.elim (by omega) (by omega),
      fun h => hout.2.2.elim (by omega) (by omega),
      hnotEr, fun h => hnotAfter ⟨by omega, by omega⟩, fun h => hnotAfter ⟨by omega, by omega⟩,
      fun ⟨e, he, h1, h2⟩ => by
        obtain ⟨hb1, hb2⟩ := init_thPtr_bounds (threshHeap := threshHeap) (L := L) (m := m) he
          (show a - thPtr e < L by omega)
        have haEq : thPtr e + (a - thPtr e) = a := by omega
        rw [haEq] at hb1 hb2; exact hnotAfter ⟨by omega, hb2⟩,
      fun ⟨e, he, h1, h2⟩ => by
        obtain ⟨hb1, hb2⟩ := init_recPtr_bounds (threshHeap := threshHeap) (L := L) (m := m) he
          (show a - recPtr e < 2 + 4 * L by omega)
        have haEq : recPtr e + (a - recPtr e) = a := by omega
        rw [haEq] at hb1 hb2; exact hnotAfter ⟨by omega, hb2⟩,
      by omega⟩
  have htag_def (a : ℕ) :
      open Classical in
      tagFn a =
        if root ≤ a ∧ a < root + 16 then 1
        else if rootGraph ≤ a ∧ a < rootGraph + dynGraphSize G.n eCap then 20
        else if len0Buf ≤ a ∧ a < table then 23 + d
        else if table ≤ a ∧ a < n0Cell then 3
        else if (n0Cell ≤ a ∧ a < levelMeta) ∨ (selectHeap ≤ a ∧ a < handle) then 21 + d
        else if levelMeta ≤ a ∧ a < selectHeap then 22 + d
        else if handle ≤ a ∧ a < levelTable then 2
        else if levelTable ≤ a ∧ a < branchTable + (d + 1) then 4
        else if metaStatic a then 23 + d
        else if levelsEnd ≤ a ∧ a < freshCounter then 5
        else if a = freshCounter then 6
        else if forward ≤ a ∧ a < inverse then 7
        else if inverse ≤ a ∧ a < edgeThresholds then 8
        else if edgeThresholds ≤ a ∧ a < treeHeap then 12
        else if slots ≤ a ∧ a < names then 9
        else if names ≤ a ∧ a < slotThresholds then 10
        else if slotThresholds ≤ a ∧ a < edgeRecords then 11
        else if edgeRecords ≤ a ∧ a < offReadyList then 13
        else if offReadyList ≤ a ∧ a < inOffReady then 14
        else if inOffReady ≤ a ∧ a < threshHeap then 15
        else if ∃ e < m, thPtr e ≤ a ∧ a < thPtr e + L then 17
        else if ∃ e < m, recPtr e ≤ a ∧ a < recPtr e + (2 + 4 * L) then 18
        else if Rtree.foot treeHeap yTree a then 16
        else if (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L 0 (model.chain.G d).E).foot (mem (levelTable + d)) yTerm a then 19
        else if h : ∃ i < d, Rcore.foot (mem (levelTable + i)) (yCore i) a then 21 + Classical.choose h
        else 0 := rfl
  have htag_ge_lev (a : ℕ) (ha : levelsEnd ≤ a) :
      open Classical in
      tagFn a =
        if levelsEnd ≤ a ∧ a < freshCounter then 5
        else if a = freshCounter then 6
        else if forward ≤ a ∧ a < inverse then 7
        else if inverse ≤ a ∧ a < edgeThresholds then 8
        else if edgeThresholds ≤ a ∧ a < treeHeap then 12
        else if slots ≤ a ∧ a < names then 9
        else if names ≤ a ∧ a < slotThresholds then 10
        else if slotThresholds ≤ a ∧ a < edgeRecords then 11
        else if edgeRecords ≤ a ∧ a < offReadyList then 13
        else if offReadyList ≤ a ∧ a < inOffReady then 14
        else if inOffReady ≤ a ∧ a < threshHeap then 15
        else if ∃ e < m, thPtr e ≤ a ∧ a < thPtr e + L then 17
        else if ∃ e < m, recPtr e ≤ a ∧ a < recPtr e + (2 + 4 * L) then 18
        else if Rtree.foot treeHeap yTree a then 16
        else if (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L 0 (model.chain.G d).E).foot (mem (levelTable + d)) yTerm a then 19
        else if h : ∃ i < d, Rcore.foot (mem (levelTable + i)) (yCore i) a then 21 + Classical.choose h
        else 0 := by
    rw [htag_def, ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega),
      ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (hnotMeta_of_ge a ha)]
  have htag_tail (a : ℕ)
      (hout : OutsideInitSlotTables slots names slotThresholds m G.n a)
      (hnotSt : ¬ InitChainStaticAddr rootGraph levelTable branchTable edgeRecords edgeThresholds
        d m L G model.chain.toTreeChain.chainTree recPtr extraStatic a) :
      open Classical in
      tagFn a =
        if Rtree.foot treeHeap yTree a then 16
        else if (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L 0 (model.chain.G d).E).foot (mem (levelTable + d)) yTerm a then 19
        else if h : ∃ i < d, Rcore.foot (mem (levelTable + i)) (yCore i) a then 21 + Classical.choose h
        else 0 := by
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, h22, _⟩ := hnot_pre a hout hnotSt
    rw [htag_def]
    simp only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, h17, h18,
      h19, h20, h21, h22, ↓reduceIte]
  have htags : SolverTagsAt root m model tok mem := by
    refine ⟨fun _ h => Or.inl h, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j hj; change tagFn (root + j) = 1; rw [htag_def, ite_eq_left (by omega)]
    · intro j hj; change tagFn (handle + j) = 2; rw [htag_def]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; change tagFn (table + j) = 3; rw [htag_def]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; change tagFn (levelTable + j) = 4; rw [htag_def]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; change tagFn (levelsEnd + j) = 5; rw [htag_ge_lev _ (by omega), ite_eq_left (by omega)]
    · change tagFn freshCounter = 6; rw [htag_ge_lev _ (by omega), ite_eq_right (by omega), ite_eq_left rfl]
    · intro j hj; change tagFn (forward + j) = 7; rw [htag_ge_lev _ (by omega)]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; change j < m at hj; change tagFn (inverse + j) = 8; rw [htag_ge_lev _ (by omega)]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; change j < m at hj; change tagFn (slots + j) = 9; rw [htag_ge_lev _ (by omega)]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; rw [hsn] at hj; change tagFn (names + j) = 10; rw [htag_ge_lev _ (by omega)]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; rw [hsn] at hj; change tagFn (slotThresholds + j) = 11; rw [htag_ge_lev _ (by omega)]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; change j < m at hj; change tagFn (edgeThresholds + j) = 12; rw [htag_ge_lev _ (by omega)]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; change j < m at hj; change tagFn (edgeRecords + j) = 13; rw [htag_ge_lev _ (by omega)]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; change j < m at hj; change tagFn (offReadyList + j) = 14; rw [htag_ge_lev _ (by omega)]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro j hj; change j < m at hj; change tagFn (inOffReady + j) = 15; rw [htag_ge_lev _ (by omega)]; (repeat rw [ite_eq_right (by omega)]); rw [ite_eq_left (by omega)]
    · intro a ha; change tagFn a = 16; rw [htag_tail a (htreeDisj a ha).1 (htreeDisj a ha).2, ite_eq_left ha]
    · intro e he
      have hem : e < m := by rw [hExtG, hGE] at he; exact Finset.mem_range.mp he
      have hptr := hptrAt e hem
      refine ⟨fun j hj => ?_, fun _ j hj => ?_⟩
      · have hne_pre := init_thPtr_bounds (threshHeap := threshHeap) (L := L) (m := m) hem hj
        change tagFn (mem (edgeThresholds + model.extToInt e) + j) = 17
        rw [hExtToInt, id, hptr.1, htag_ge_lev _ (by omega)]
        repeat rw [ite_eq_right (by omega)]
        exact ite_eq_left ⟨e, hem, by dsimp only [thPtr]; omega, by dsimp only [thPtr]; omega⟩
      · have hne_pre := init_recPtr_bounds (threshHeap := threshHeap) (L := L) (m := m) hem hj
        have hnot17 : ¬ ∃ e' < m, thPtr e' ≤ recPtr e + j ∧ recPtr e + j < thPtr e' + L := by
          rintro ⟨e', _, hlo, hhi⟩
          have heq := init_thPtr_recPtr_disjoint (threshHeap := threshHeap) (L := L) (e := e') (e' := e)
            (j := recPtr e + j - thPtr e') (j' := j) (by omega) hj
          dsimp only [thPtr, recPtr] at hlo heq; omega
        change tagFn (mem (edgeRecords + model.extToInt e) + j) = 18
        rw [hExtToInt, id, hptr.2]
        change tagFn (recPtr e + j) = 18
        rw [htag_ge_lev _ (by dsimp only [recPtr]; omega)]
        repeat rw [ite_eq_right (by dsimp only [recPtr]; omega)]
        exact ite_eq_left ⟨e, hem, by omega, by omega⟩
    · intro a ha
      have haP := (lastLevelRepresentation_foot_indep_P vcLast ecLast 4 L 0 P _ _ _ _).mp ha
      have hf := hcoresAt.2.2.2 a haP
      change tagFn a = 19
      rw [htag_tail a hf.2.1 hf.2.2.1, ite_eq_right hf.2.2.2.1, ite_eq_left ha]
    · intro a hlo hhi
      change rootGraph ≤ a at hlo; rw [hExtG] at hhi
      change a < rootGraph + dynGraphSize G.n eCap at hhi
      change tagFn a = 20; rw [htag_def, ite_eq_right (by omega), ite_eq_left ⟨hlo, hhi⟩]
    · intro i hi a ha
      have hf := (hcoresAt.1 i hi).2.2 a ha
      have hnt : ¬ (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L 0 (model.chain.G d).E).foot (mem (levelTable + d)) yTerm a := fun ht =>
        hf.2.2.2.2.2 ((lastLevelRepresentation_foot_indep_P vcLast ecLast 4 L 0 P _ _ _ _).mp ht)
      have hex : ∃ j < d, Rcore.foot (mem (levelTable + j)) (yCore j) a := ⟨i, hi, ha⟩
      have hch : Classical.choose hex = i := by
        by_contra hne
        exact hf.2.2.2.2.1 _ (Classical.choose_spec hex).1 hne (Classical.choose_spec hex).2
      change tagFn a = 21 + i
      rw [htag_tail a hf.2.1 hf.2.2.1, ite_eq_right hf.2.2.2.1, ite_eq_right hnt,
        dite_eq_left hex, hch]
  have hCapsInv : SolverLevelCapsInv P V G.n eCap model tok mem := by
    rw [solverLevelCapsInv_iff_metaCaps]
    have hTag21 (a : ℕ) (h : (n0Cell ≤ a ∧ a < levelMeta) ∨ (selectHeap ≤ a ∧ a < handle)) :
        tok.tag a = 21 + d := by
      change tagFn a = 21 + d; rw [htag_def]; (repeat rw [ite_eq_right (by omega)])
      exact ite_eq_left h
    have hTag22 (a : ℕ) (hlo : levelMeta ≤ a) (hhi : a < selectHeap) : tok.tag a = 22 + d := by
      change tagFn a = 22 + d; rw [htag_def]; (repeat rw [ite_eq_right (by omega)])
      exact ite_eq_left ⟨hlo, hhi⟩
    have hTagLen0 (a : ℕ) (hlo : len0Buf ≤ a) (hhi : a < table) : tok.tag a = 23 + d := by
      change tagFn a = 23 + d; rw [htag_def]; (repeat rw [ite_eq_right (by omega)])
      exact ite_eq_left ⟨hlo, hhi⟩
    have hTagMeta (a : ℕ) (hm : metaStatic a) : tok.tag a = 23 + d := by
      have hge := (hMetaGe a hm).1
      change tagFn a = 23 + d; rw [htag_def]; (repeat rw [ite_eq_right (by omega)])
      exact ite_eq_left hm
    have heLpos : 0 < eCap * L := Nat.mul_pos (lt_of_lt_of_le hmPos hmLeECap) hLpos
    refine ⟨⟨hN0Val, hTag21 n0Cell (Or.inl ⟨le_rfl, by omega⟩),
        hTag21 selectHeap (Or.inr ⟨le_rfl, by omega⟩),
        hTag21 (selectHeap + 1) (Or.inr ⟨by omega, by omega⟩)⟩,
      fun j hj => Or.inr ⟨j, hj, rfl⟩,
      fun j hj => hMTab j hj,
      fun j hj => hTag21 (lvlMTable + j) (Or.inl ⟨by omega, by omega⟩),
      fun j hj => hTag22 (levelMeta + j) (by omega) (by omega),
      fun j hj => ?_⟩
    by_cases hj0 : j = 0
    · subst hj0
      refine ⟨by simpa [tok, hMetaG0] using hDG0,
        by simpa [tok, hMetaL0] using hLen0, ?_, ?_, ?_⟩
      · change tok.owned (mem (levelMeta + 0))
        rw [Nat.add_zero, show mem levelMeta = len0Buf from hMetaL0]
        exact Or.inl (by rw [show tagFn len0Buf = 23 + d from hTagLen0 len0Buf le_rfl (by omega)]; omega)
      · intro a hlo hhi
        rw [Nat.add_zero, show mem (solverLevelMetaAddr tok.table d) = len0Buf from hMetaL0] at hlo hhi
        exact hTagLen0 a hlo (by omega)
      · intro a hlo hhi
        rw [Nat.add_zero, show mem (solverLevelMetaAddr tok.table d + d) = rootGraph from hMetaG0] at hlo hhi
        simp only [↓reduceIte]; change tagFn a = 20; rw [htag_def, ite_eq_right (by omega), ite_eq_left ⟨hlo, hhi⟩]
    · have hj1 : 1 ≤ j := Nat.pos_of_ne_zero hj0
      obtain ⟨hDGj, hEVj, hLlo, hLhi, hGlo, hGhi⟩ := hMetaLvls j hj1 hj
      refine ⟨hDGj, hEVj,
        Or.inl (by rw [show tagFn (mem (levelMeta + j)) = 23 + d from
          hTagMeta _ ⟨j, hj1, hj, Or.inl ⟨le_rfl, by dsimp only [metaL]; omega⟩⟩]; omega),
        fun a hlo hhi => hTagMeta a ⟨j, hj1, hj, Or.inl ⟨hlo, hhi⟩⟩,
        fun a hlo hhi => by
          rw [ite_eq_right hj0]
          exact hTagMeta a ⟨j, hj1, hj, Or.inr ⟨hlo, hhi⟩⟩⟩
  refine ⟨htags, hCapsInv, fun a ha => ?_⟩
  rcases ha with hown | htreeF | ⟨i, hi, hcoreF⟩
  · rcases hown with hown | ⟨j, hj, rfl⟩
    · rw [htag_def] at hown
      by_cases c1 : root ≤ a ∧ a < root + 16; · omega
      by_cases c20 : rootGraph ≤ a ∧ a < rootGraph + dynGraphSize G.n eCap; · omega
      by_cases cL0 : len0Buf ≤ a ∧ a < table; · omega
      by_cases c3 : table ≤ a ∧ a < n0Cell; · omega
      by_cases c21d : (n0Cell ≤ a ∧ a < levelMeta) ∨ (selectHeap ≤ a ∧ a < handle); · omega
      by_cases c22d : levelMeta ≤ a ∧ a < selectHeap; · omega
      by_cases c2 : handle ≤ a ∧ a < levelTable; · omega
      by_cases c4 : levelTable ≤ a ∧ a < branchTable + (d + 1); · omega
      by_cases cM : metaStatic a; · have := hMetaGe a cM; omega
      by_cases c5 : levelsEnd ≤ a ∧ a < freshCounter; · omega
      by_cases c6 : a = freshCounter; · omega
      by_cases c7 : forward ≤ a ∧ a < inverse; · omega
      by_cases c8 : inverse ≤ a ∧ a < edgeThresholds; · omega
      by_cases c12 : edgeThresholds ≤ a ∧ a < treeHeap; · omega
      by_cases c9 : slots ≤ a ∧ a < names; · omega
      by_cases c10 : names ≤ a ∧ a < slotThresholds; · omega
      by_cases c11 : slotThresholds ≤ a ∧ a < edgeRecords; · omega
      by_cases c13 : edgeRecords ≤ a ∧ a < offReadyList; · omega
      by_cases c14 : offReadyList ≤ a ∧ a < inOffReady; · omega
      by_cases c15 : inOffReady ≤ a ∧ a < threshHeap; · omega
      by_cases c17 : ∃ e < m, thPtr e ≤ a ∧ a < thPtr e + L
      · rcases c17 with ⟨e, he, hlo, hhi⟩
        have hb := init_thPtr_bounds (threshHeap := threshHeap) (L := L) (m := m) he (show a - thPtr e < L by omega)
        rw [show thPtr e + (a - thPtr e) = a by omega] at hb; omega
      by_cases c18 : ∃ e < m, recPtr e ≤ a ∧ a < recPtr e + (2 + 4 * L)
      · rcases c18 with ⟨e, he, hlo, hhi⟩
        have hb := init_recPtr_bounds (threshHeap := threshHeap) (L := L) (m := m) he (show a - recPtr e < 2 + 4 * L by omega)
        rw [show recPtr e + (a - recPtr e) = a by omega] at hb; omega
      by_cases c16 : Rtree.foot treeHeap yTree a
      · exact ⟨(hnot_pre a (htreeDisj a c16).1 (htreeDisj a c16).2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hfootTreeLt a c16⟩
      by_cases c19 : (LastLevelProgram.lastLevelRepresentation vcLast ecLast 4 L 0 (model.chain.G d).E).foot (mem (levelTable + d)) yTerm a
      · have hf := hcoresAt.2.2.2 a ((lastLevelRepresentation_foot_indep_P vcLast ecLast 4 L 0 P _ _ _ _).mp c19)
        exact ⟨(hnot_pre a hf.2.1 hf.2.2.1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hf.1⟩
      by_cases c21 : ∃ i < d, Rcore.foot (mem (levelTable + i)) (yCore i) a
      · rcases c21 with ⟨i, hi, hfi⟩
        have hf := (hcoresAt.1 i hi).2.2 a hfi
        exact ⟨(hnot_pre a hf.2.1 hf.2.2.1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hf.1⟩
      simp only [c1, c20, cL0, c3, c21d, c22d, c2, c4, cM, c5, c6, c7, c8, c12, c9, c10, c11, c13, c14, c15, c17, c18, c16, c19, c21, ↓reduceIte, ↓reduceDIte] at hown
      exact (hown rfl).elim
    · have hcb := hCoreBds j hj
      dsimp only [levelTable, handle, d] at *
      change root ≤ mem (solverHandleAddr table cfg.P.d + 18 + j) ∧ mem (solverHandleAddr table cfg.P.d + 18 + j) < finalHeap; omega
  · exact ⟨(hnot_pre a (htreeDisj a htreeF).1 (htreeDisj a htreeF).2).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hfootTreeLt a htreeF⟩
  · have hf := (hcoresAt.1 i hi).2.2 a hcoreF
    exact ⟨(hnot_pre a hf.2.1 hf.2.2.1).2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2, hf.1⟩

end MinCostFlow.MinRatio
end
