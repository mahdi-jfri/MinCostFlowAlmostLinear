module

public import MinCostFlow.MinRatio.OrdSparseCoreHelpers
public import MinCostFlow.MinRatio.WireSuffixEditsBase
public import MinCostFlow.MinRatio.WireShiftTermPhases
import WordRAM.Tactic

/-!
# Chain runtime, tree-update, and suffix-forest algebra (`WireChainAlgebra`)

Supplies exact algebraic identities for `Chain.Ordered.rebuildSuffix`,
`Chain.Ordered.algorithm1_shift` (`i₀ < d`), and `Chain.Ordered.algorithm1_rebuild` (`i₀ ≤ d`):
1. `ordRebuildSuffix_extra`: exact `cEnc`, `cDec`, and terminal `(lastRes, lastCost)` values of
   `Chain.Ordered.rebuildSuffix`.
2. `ordAlgorithm1_shift_exact` & `ordAlgorithm1_shift_coreAt_eq_zeroExtension`: exact level-by-level
   description of `(Chain.Ordered.algorithm1_shift T L P chain i₀).1` for `i₀ < P.d`.
3. `shiftDeep_totalRuntime_sub`, `shiftDeep_totalTreeUpdates_sub`, `rebuild_totalRuntime_sub`,
   `rebuild_totalTreeUpdates_sub`: exact `totalRuntime` and `totalTreeUpdates` deltas.
4. `chainSuffixForests`, `chainTree_E_eq_prefix_union_suffix`, `treeEditDiff_chainSuffix`:
   splits `chainTree.E` into prefix `[0, first)` and suffix `[first, d]` for `wireSuffixPackEditsBody`.
-/

public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore.Program

section RebuildSuffixExtra

/-- Exact `cEnc`, `cDec`, and terminal `(lastRes, lastCost)` outputs of
`Chain.Ordered.rebuildSuffix`. -/
theorem ordRebuildSuffix_extra (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ), idx + rem ≤ P.d →
      ∀ (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      let res := Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      let G' := res.1
      let sc' := res.2.1
      let bran' := res.2.2.1
      let cEnc' := res.2.2.2.2.1
      let cDec' := res.2.2.2.2.2.1
      let lastRes := res.2.2.2.2.2.2.2.1
      let lastCost := res.2.2.2.2.2.2.2.2
      (∀ m < idx, cEnc' m = cEnc m ∧ cDec' m = cDec m) ∧
      (∀ j, idx ≤ j → j < idx + rem → cEnc' j = 0 ∧ cDec' j = 0) ∧
      (let Cfin : TreeChain :=
        { d := P.d, k := P.k, G := G', lsfs := fun m => T.lsfs (sc' m), bran := bran',
          S := fun m => T.S (sc' m), emb := fun m => T.emb (sc' m),
          lastK := 1, lastLSFs := fun _ => ⟨G' (idx + rem), ⟨G' (idx + rem), ∅⟩, fun _ => 1⟩,
          lastBran := 0 }
       lastRes = L.build (G' (idx + rem)) (Cfin.chainLen ℓ₀ (idx + rem)) ∧
       lastCost = L.cost (G' (idx + rem))) := by
  intro rem
  induction rem with
  | zero =>
    intro idx _ G sc bran upd cEnc cDec cFwd
    refine ⟨fun _ _ => ⟨rfl, rfl⟩, fun _ h1 h2 => by omega, ⟨rfl, rfl⟩⟩
  | succ rem ih =>
    intro idx hbound G sc bran upd cEnc cDec cFwd
    dsimp only [Chain.Ordered.rebuildSuffix]
    let Cstep : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    let sc_i := T.initOrd P.k (lvlM idx) N₀ (G idx) (Cstep.chainLen ℓ₀ idx) (Cstep.chainGrad g₀ idx)
      (Chain.Ordered.chainLevelOrd T G sc bran idx)
    let G1 := fun j => if j = idx + 1 then T.S sc_i 0 else G j
    let sc1 := fun j => if j = idx then sc_i else sc j
    let bran1 := fun j => if j = idx then 0 else bran j
    let upd1 := fun j => if j = idx then 0 else upd j
    let cEnc1 := fun j => if j = idx then 0 else cEnc j
    let cDec1 := fun j => if j = idx then 0 else cDec j
    let cFwd1 := fun j => if j = idx then 0 else cFwd j
    obtain ⟨hPre, hZero, hLast⟩ := ih (idx + 1) (by omega) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      obtain ⟨he, hd⟩ := hPre m (by omega)
      dsimp only [cEnc1, cDec1] at he hd
      simp only [show m ≠ idx by omega, ↓reduceIte] at he hd
      exact ⟨he, hd⟩
    · intro j hj1 hj2
      by_cases hjeq : j = idx
      · subst hjeq
        obtain ⟨he, hd⟩ := hPre j (Nat.lt_succ_self j)
        dsimp only [cEnc1, cDec1] at he hd
        simp only [↓reduceIte] at he hd
        exact ⟨he, hd⟩
      · exact hZero j (by omega) (by omega)
    · have hadd : idx + 1 + rem = idx + (rem + 1) := by omega
      rw [← hadd]
      exact hLast

end RebuildSuffixExtra

section ShiftDeepExact

private lemma chainLen_congr {C₁ C₂ : TreeChain} {ℓ : ℕ → ℝ} {k : ℕ}
    (h : ∀ m < k, C₁.activeLSF m = C₂.activeLSF m) :
    C₁.chainLen ℓ k = C₂.chainLen ℓ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [TreeChain.chainLen]
    rw [h k (Nat.lt_succ_self k), ih (fun m hm => h m (Nat.lt_succ_of_lt hm))]

private lemma chainGrad_congr {C₁ C₂ : TreeChain} {g : ℕ → ℝ} {k : ℕ}
    (hG : ∀ m < k, C₁.G m = C₂.G m) (hL : ∀ m < k, C₁.activeLSF m = C₂.activeLSF m) :
    C₁.chainGrad g k = C₂.chainGrad g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [TreeChain.chainGrad]
    rw [hG k (Nat.lt_succ_self k), hL k (Nat.lt_succ_self k),
      ih (fun m hm => hG m (Nat.lt_succ_of_lt hm)) (fun m hm => hL m (Nat.lt_succ_of_lt hm))]

/-- Complete level-by-level characterization of `(Chain.Ordered.algorithm1_shift T L P chain i₀).1`
for a non-terminal shift `i₀ < P.d`. -/
theorem ordAlgorithm1_shift_exact (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (chain : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d) :
    let next := (Chain.Ordered.algorithm1_shift T L P chain i₀).1
    let newBran := (chain.bran i₀ + 1) % P.k
    let sc_i0 := T.restart (chain.scState i₀) newBran
    (∀ m ≤ i₀, next.G m = chain.G m) ∧
    (∀ m < i₀, next.scState m = chain.scState m ∧ next.bran m = chain.bran m ∧
      next.updCount m = chain.updCount m ∧ next.curEnc m = chain.curEnc m ∧
      next.curDecUpdates m = chain.curDecUpdates m) ∧
    next.scState i₀ = sc_i0 ∧ next.bran i₀ = newBran ∧
    next.updCount i₀ = chain.updCount i₀ ∧ next.curEnc i₀ = chain.curEnc i₀ ∧
    next.curDecUpdates i₀ = 0 ∧ next.G (i₀ + 1) = T.S sc_i0 newBran ∧
    (∀ j, i₀ + 1 ≤ j → j < P.d →
      next.scState j = T.initOrd P.k (chain.lvlM j) chain.N₀ (next.G j)
        (next.toTreeChain.chainLen chain.ℓ j) (next.toTreeChain.chainGrad chain.g j)
        (next.levelOrd j) ∧
      next.G (j + 1) = T.S (next.scState j) 0 ∧
      next.bran j = 0 ∧ next.updCount j = 0 ∧ next.curEnc j = 0 ∧ next.curDecUpdates j = 0) ∧
    (next.lastK, next.lastLSFs) = L.build (next.G P.d) (next.toTreeChain.chainLen chain.ℓ P.d) ∧
    next.lastBran = 0 ∧ next.curLastCost = L.cost (next.G P.d) ∧
    next.curLastTreeUpdates = 0 ∧
    next.ℓ = chain.ℓ ∧ next.g = chain.g ∧ next.lvlM = chain.lvlM ∧ next.N₀ = chain.N₀ := by
  dsimp only
  set newBran := (chain.bran i₀ + 1) % P.k
  set sc_i0 := T.restart (chain.scState i₀) newBran
  set G0 := fun j => if j = i₀ + 1 then T.S sc_i0 newBran else chain.G j
  set sc0 := fun j => if j = i₀ then sc_i0 else chain.scState j
  set bran0 := fun j => if j = i₀ then newBran else chain.bran j
  set cEnc0 := fun j => if j = i₀ + 1 then 0 else chain.curEnc j
  set cDec0 := fun j => if j = i₀ then 0 else chain.curDecUpdates j
  set res := Chain.Ordered.rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g
    (P.d - (i₀ + 1)) (i₀ + 1) G0 sc0 bran0 chain.updCount cEnc0 cDec0 chain.curFwd
  set next := (Chain.Ordered.algorithm1_shift T L P chain i₀).1
  have hG : ∀ m, next.G m = res.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte, res, G0, sc0, bran0, cEnc0, cDec0,
      newBran, sc_i0]
  have hSc : ∀ m, next.scState m = res.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte, res, G0, sc0, bran0, cEnc0, cDec0,
      newBran, sc_i0]
  have hBr : ∀ m, next.bran m = res.2.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte, res, G0, sc0, bran0, cEnc0, cDec0,
      newBran, sc_i0]
  have hUpd : ∀ m, next.updCount m = res.2.2.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte, res, G0, sc0, bran0, cEnc0, cDec0,
      newBran, sc_i0]
  have hEnc : ∀ m, next.curEnc m = res.2.2.2.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte, res, G0, sc0, bran0, cEnc0, cDec0,
      newBran, sc_i0]
  have hDec : ∀ m, next.curDecUpdates m = res.2.2.2.2.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte, res, G0, sc0, bran0, cEnc0, cDec0,
      newBran, sc_i0]
  obtain ⟨hGpre, hSBpre, hCore⟩ :=
    ordRebuildSuffix_prefix_and_coreAt T L P chain.lvlM chain.N₀ chain.ℓ chain.g
      (P.d - (i₀ + 1)) (i₀ + 1) (by omega) G0 sc0 bran0 chain.updCount cEnc0 cDec0 chain.curFwd
  obtain ⟨hEDpre, hEDzero, hLast⟩ :=
    ordRebuildSuffix_extra T L P chain.lvlM chain.N₀ chain.ℓ chain.g
      (P.d - (i₀ + 1)) (i₀ + 1) (by omega) G0 sc0 bran0 chain.updCount cEnc0 cDec0 chain.curFwd
  have hadd : i₀ + 1 + (P.d - (i₀ + 1)) = P.d := by omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro m hm
    rw [hG m, hGpre m (by omega)]
    simp [G0, show m ≠ i₀ + 1 by omega]
  · intro m hm
    obtain ⟨h1, h2, h3⟩ := hSBpre m (by omega)
    obtain ⟨h4, h5⟩ := hEDpre m (by omega)
    rw [hSc m, hBr m, hUpd m, hEnc m, hDec m, h1, h2, h3, h4, h5]
    simp [sc0, bran0, cEnc0, cDec0, show m ≠ i₀ by omega, show m ≠ i₀ + 1 by omega]
  · rw [hSc i₀, (hSBpre i₀ (by omega)).1]; simp [sc0]
  · rw [hBr i₀, (hSBpre i₀ (by omega)).2.1]; simp [bran0]
  · rw [hUpd i₀, (hSBpre i₀ (by omega)).2.2]
  · rw [hEnc i₀, (hEDpre i₀ (by omega)).1]; simp [cEnc0]
  · rw [hDec i₀, (hEDpre i₀ (by omega)).2]; simp [cDec0]
  · rw [hG (i₀ + 1), hGpre (i₀ + 1) le_rfl]; simp [G0]
  · intro j hj1 hj2
    obtain ⟨hscj, hGj1, hbrj, hupj⟩ := hCore j hj1 (by omega)
    obtain ⟨hcej, hcdj⟩ := hEDzero j hj1 (by omega)
    have hlen :
        ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
           bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
           lastK := 1, lastLSFs := fun _ => ⟨res.1 j, ⟨res.1 j, ∅⟩, fun _ => 1⟩,
           lastBran := 0 } : TreeChain).chainLen chain.ℓ j =
        next.toTreeChain.chainLen chain.ℓ j :=
      chainLen_congr (fun m hm => by
        dsimp only [TreeChain.activeLSF, ChainState.toTreeChain]
        simp only [show m < P.d by omega, ↓reduceIte, hSc m, hBr m])
    have hgrad :
        ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
           bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
           lastK := 1, lastLSFs := fun _ => ⟨res.1 j, ⟨res.1 j, ∅⟩, fun _ => 1⟩,
           lastBran := 0 } : TreeChain).chainGrad chain.g j =
        next.toTreeChain.chainGrad chain.g j :=
      chainGrad_congr (fun m _ => (hG m).symm) (fun m hm => by
        dsimp only [TreeChain.activeLSF, ChainState.toTreeChain]
        simp only [show m < P.d by omega, ↓reduceIte, hSc m, hBr m])
    have hord : Chain.Ordered.chainLevelOrd T res.1 res.2.1 res.2.2.1 j = next.levelOrd j := by
      unfold ChainState.levelOrd Chain.Ordered.chainLevelOrd
      split_ifs with h0
      · subst h0; exact congrArg sortedEnds (hG 0).symm
      · rw [hSc (j - 1), hBr (j - 1)]
    refine ⟨?_, ?_, (hBr j).trans hbrj, (hUpd j).trans hupj, (hEnc j).trans hcej, (hDec j).trans hcdj⟩
    · rw [hSc j, hscj, hG j, hlen, hgrad, hord]
    · rw [hG (j + 1), hGj1, hSc j]
  · have hlastEq : (next.lastK, next.lastLSFs) = res.2.2.2.2.2.2.2.1 := by
      simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte, res, G0, sc0, bran0, cEnc0, cDec0,
        newBran, sc_i0, Prod.mk.eta]
    rw [hlastEq, hLast.1, hadd, ← hG P.d]
    congr 1
    exact chainLen_congr (fun m hm => by
      dsimp only [TreeChain.activeLSF, ChainState.toTreeChain]
      simp only [show m < P.d by omega, ↓reduceIte, hSc m, hBr m]; rfl)
  · simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte]
  · have hlc : next.curLastCost = res.2.2.2.2.2.2.2.2 := by
      simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte, res, G0, sc0, bran0, cEnc0, cDec0,
        newBran, sc_i0]
    rw [hlc, hLast.2, hadd, hG P.d]
  · simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte]
  · simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte]
  · simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte]
  · simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte]
  · simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte]

/-- Zero-extension core-state agreement for `Chain.Ordered.algorithm1_shift` at `i₀ < P.d`. -/
theorem ordAlgorithm1_shift_coreAt_eq_zeroExtension
    {T : SparseCoreRestartTool} (hEq : ToolInitOrdEqOnE T)
    (L : LastLevelTool) (P : ChainParams) (chain : ChainState T P)
    {i₀ level : ℕ} (hi₀ : i₀ < P.d) (hfirst : i₀ + 1 ≤ level) (hlevel : level < P.d) :
    let next := (Chain.Ordered.algorithm1_shift T L P chain i₀).1
    let G := next.G level
    let len := next.toTreeChain.chainLen chain.ℓ level
    let grad := next.toTreeChain.chainGrad chain.g level
    next.scState level = T.initOrd P.k (chain.lvlM level) chain.N₀ G
      (fun a => if a ∈ G.E then len a else 0)
      (fun a => if a ∈ G.E then grad a else 0)
      (next.levelOrd level) := by
  dsimp only
  have hEx := ordAlgorithm1_shift_exact T L P chain hi₀
  have hst := (hEx.2.2.2.2.2.2.2.2.1 level hfirst hlevel).1
  exact hst.trans (hEq _ _ _ _ _ _ _ _ _ (fun e he => by simp [he]))

/-- Exact `chainLevelOrdAbs` agreement on levels `0 .. i₀` under a non-terminal shift at `i₀ < P.d`. -/
theorem ordAlgorithm1_shift_levelOrdAbs_le (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (chain : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d) :
    let next := (Chain.Ordered.algorithm1_shift T L P chain i₀).1
    let newBran := (chain.bran i₀ + 1) % P.k
    (∀ j < i₀, chainLevelOrdAbs next j = chainLevelOrdAbs chain j) ∧
    chainLevelOrdAbs next i₀ =
      ⟨T.restart (chain.scState i₀) newBran, chain.G i₀, chain.levelOrd i₀, chain.updCount i₀⟩ := by
  dsimp only
  have hEx := ordAlgorithm1_shift_exact T L P chain hi₀
  have hGpre := hEx.1
  have hPre := hEx.2.1
  have hOrd : ∀ j ≤ i₀, (Chain.Ordered.algorithm1_shift T L P chain i₀).1.levelOrd j = chain.levelOrd j := by
    intro j hj
    unfold ChainState.levelOrd Chain.Ordered.chainLevelOrd
    split_ifs with h0
    · subst h0; exact congrArg sortedEnds (hGpre 0 (Nat.zero_le _))
    · obtain ⟨hsc, hbr, _⟩ := hPre (j - 1) (by omega)
      rw [hsc, hbr]
  refine ⟨fun j hj => ?_, ?_⟩
  · unfold chainLevelOrdAbs
    obtain ⟨hsc, _, hupd, _⟩ := hPre j hj
    rw [hsc, hGpre j (le_of_lt hj), hOrd j (le_of_lt hj), hupd]
  · unfold chainLevelOrdAbs
    rw [hEx.2.2.1, hGpre i₀ le_rfl, hOrd i₀ le_rfl, hEx.2.2.2.2.1]

end ShiftDeepExact

section RuntimeAndTreeDeltas

private lemma sum_range_split_at {n i : ℕ} (hi : i ≤ n) (f : ℕ → ℕ) :
    (Finset.range n).sum f = (Finset.range i).sum f + (Finset.Ico i n).sum f := by
  rw [← Finset.sum_union]
  · congr 1; ext x; simp only [Finset.mem_range, Finset.mem_union, Finset.mem_Ico]; omega
  · rw [Finset.disjoint_left]; intro x hx1 hx2
    simp only [Finset.mem_range, Finset.mem_Ico] at hx1 hx2; omega

/-- Exact `totalRuntime` delta for a non-terminal shift `i₀ < P.d`. -/
theorem shiftDeep_totalRuntime_sub (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (chain : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d)
    (hMono : T.cost (chain.scState i₀) ≤
      T.cost (T.restart (chain.scState i₀) ((chain.bran i₀ + 1) % P.k))) :
    let next := (Chain.Ordered.algorithm1_shift T L P chain i₀).1
    next.totalRuntime - chain.totalRuntime =
      (T.cost (next.scState i₀) - T.cost (chain.scState i₀)) +
      (Finset.Ico (i₀ + 1) P.d).sum (fun j => T.cost (next.scState j)) +
      L.cost (next.G P.d) := by
  dsimp only
  set next := (Chain.Ordered.algorithm1_shift T L P chain i₀).1
  have hEx := ordAlgorithm1_shift_exact T L P chain hi₀
  have hClosed : next.closedRuntime =
      chain.closedRuntime +
        (Finset.Ico (i₀ + 1) P.d).sum (fun j => T.cost (chain.scState j) + chain.curEnc j) +
        chain.curLastCost := by
    simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte]
  have hOldSplit :
      (Finset.range P.d).sum (fun j => T.cost (chain.scState j) + chain.curEnc j) =
      (Finset.range i₀).sum (fun j => T.cost (chain.scState j) + chain.curEnc j) +
      (T.cost (chain.scState i₀) + chain.curEnc i₀) +
      (Finset.Ico (i₀ + 1) P.d).sum (fun j => T.cost (chain.scState j) + chain.curEnc j) := by
    rw [sum_range_split_at (Nat.succ_le_of_lt hi₀), Finset.sum_range_succ]
  have hNewSplit :
      (Finset.range P.d).sum (fun j => T.cost (next.scState j) + next.curEnc j) =
      (Finset.range i₀).sum (fun j => T.cost (chain.scState j) + chain.curEnc j) +
      (T.cost (next.scState i₀) + chain.curEnc i₀) +
      (Finset.Ico (i₀ + 1) P.d).sum (fun j => T.cost (next.scState j)) := by
    rw [sum_range_split_at (Nat.succ_le_of_lt hi₀), Finset.sum_range_succ]
    have h1 : (Finset.range i₀).sum (fun j => T.cost (next.scState j) + next.curEnc j) =
        (Finset.range i₀).sum (fun j => T.cost (chain.scState j) + chain.curEnc j) :=
      Finset.sum_congr rfl (fun j hj => by
        obtain ⟨hsc, _, _, henc, _⟩ := hEx.2.1 j (Finset.mem_range.mp hj)
        rw [hsc, henc])
    have h2 : next.curEnc i₀ = chain.curEnc i₀ := hEx.2.2.2.2.2.1
    have h3 : (Finset.Ico (i₀ + 1) P.d).sum (fun j => T.cost (next.scState j) + next.curEnc j) =
        (Finset.Ico (i₀ + 1) P.d).sum (fun j => T.cost (next.scState j)) :=
      Finset.sum_congr rfl (fun j hj => by
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
        rw [(hEx.2.2.2.2.2.2.2.2.1 j hj1 hj2).2.2.2.2.1, add_zero])
    rw [h1, h2, h3]
  have hMono' : T.cost (chain.scState i₀) ≤ T.cost (next.scState i₀) := by
    rw [hEx.2.2.1]; exact hMono
  have hLastCost : next.curLastCost = L.cost (next.G P.d) := hEx.2.2.2.2.2.2.2.2.2.2.2.1
  unfold ChainState.totalRuntime
  rw [hClosed, hOldSplit, hNewSplit, hLastCost]
  omega

/-- Exact `totalTreeUpdates` delta for a non-terminal shift `i₀ < P.d`. -/
theorem shiftDeep_totalTreeUpdates_sub (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (chain : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d) :
    let next := (Chain.Ordered.algorithm1_shift T L P chain i₀).1
    next.totalTreeUpdates - chain.totalTreeUpdates =
      (diffTreeChanges chain.toTreeChain.chainTree.E next.toTreeChain.chainTree.E).length := by
  dsimp only
  set next := (Chain.Ordered.algorithm1_shift T L P chain i₀).1
  have hEx := ordAlgorithm1_shift_exact T L P chain hi₀
  have hClosed : next.closedTreeUpdates =
      chain.closedTreeUpdates +
        (Finset.Ico i₀ P.d).sum (fun j => chain.curDecUpdates j) +
        chain.curLastTreeUpdates +
        (diffTreeChanges chain.toTreeChain.chainTree.E next.toTreeChain.chainTree.E).length := by
    simp only [next, Chain.Ordered.algorithm1_shift, hi₀, ↓reduceDIte]
    rfl
  have hOldSplit :
      (Finset.range P.d).sum (fun j => chain.curDecUpdates j) =
      (Finset.range i₀).sum (fun j => chain.curDecUpdates j) +
      (Finset.Ico i₀ P.d).sum (fun j => chain.curDecUpdates j) :=
    sum_range_split_at (le_of_lt hi₀) _
  have hNewSplit :
      (Finset.range P.d).sum (fun j => next.curDecUpdates j) =
      (Finset.range i₀).sum (fun j => chain.curDecUpdates j) := by
    rw [sum_range_split_at (le_of_lt hi₀)]
    have h1 : (Finset.range i₀).sum (fun j => next.curDecUpdates j) =
        (Finset.range i₀).sum (fun j => chain.curDecUpdates j) :=
      Finset.sum_congr rfl (fun j hj => (hEx.2.1 j (Finset.mem_range.mp hj)).2.2.2.2)
    have h2 : (Finset.Ico i₀ P.d).sum (fun j => next.curDecUpdates j) = 0 :=
      Finset.sum_eq_zero (fun j hj => by
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
        by_cases hjeq : j = i₀
        · subst hjeq; exact hEx.2.2.2.2.2.2.1
        · exact (hEx.2.2.2.2.2.2.2.2.1 j (by omega) hj2).2.2.2.2.2)
    rw [h1, h2, add_zero]
  unfold ChainState.totalTreeUpdates
  rw [hClosed, hOldSplit, hNewSplit, hEx.2.2.2.2.2.2.2.2.2.2.2.2.1]
  omega

/-- Exact `totalRuntime` delta for `Chain.Ordered.algorithm1_rebuild` at `i₀ < P.d`. -/
theorem rebuild_totalRuntime_sub (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (chain : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d)
    (Gnew : MGraph) (extraEnc : ℕ) :
    let next := (Chain.Ordered.algorithm1_rebuild T L P chain i₀ Gnew extraEnc).1
    next.totalRuntime - chain.totalRuntime =
      (Finset.Ico i₀ P.d).sum (fun j => T.cost (next.scState j)) +
      L.cost (next.G P.d) + extraEnc := by
  dsimp only
  set next := (Chain.Ordered.algorithm1_rebuild T L P chain i₀ Gnew extraEnc).1
  set G0 := fun j => if j = i₀ then Gnew else chain.G j
  set res := Chain.Ordered.rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i₀) i₀
    G0 chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd
  obtain ⟨_, hSBpre, _⟩ :=
    ordRebuildSuffix_prefix_and_coreAt T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i₀) i₀
      (by omega) G0 chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd
  obtain ⟨hEDpre, hEDzero, hLast⟩ :=
    ordRebuildSuffix_extra T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i₀) i₀
      (by omega) G0 chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd
  have hSc : ∀ m, next.scState m = res.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hEnc : ∀ m, next.curEnc m = res.2.2.2.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hG : ∀ m, next.G m = res.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hClosed : next.closedRuntime =
      chain.closedRuntime +
        (Finset.Ico i₀ P.d).sum (fun j => T.cost (chain.scState j) + chain.curEnc j) +
        chain.curLastCost + extraEnc := by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]
  have hLastCost : next.curLastCost = L.cost (next.G P.d) := by
    have h1 : next.curLastCost = res.2.2.2.2.2.2.2.2 := by
      simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
    rw [h1, hLast.2, show i₀ + (P.d - i₀) = P.d by omega, hG P.d]
  have hOldSplit := sum_range_split_at (le_of_lt hi₀) (fun j => T.cost (chain.scState j) + chain.curEnc j)
  have hNewSplit :
      (Finset.range P.d).sum (fun j => T.cost (next.scState j) + next.curEnc j) =
      (Finset.range i₀).sum (fun j => T.cost (chain.scState j) + chain.curEnc j) +
      (Finset.Ico i₀ P.d).sum (fun j => T.cost (next.scState j)) := by
    rw [sum_range_split_at (le_of_lt hi₀)]
    congr 1
    · exact Finset.sum_congr rfl (fun j hj => by
        have hlt := Finset.mem_range.mp hj
        rw [hSc j, hEnc j, (hSBpre j hlt).1, (hEDpre j hlt).1])
    · exact Finset.sum_congr rfl (fun j hj => by
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
        rw [hEnc j, (hEDzero j hj1 (by omega)).1, add_zero])
  unfold ChainState.totalRuntime
  rw [hClosed, hOldSplit, hNewSplit, hLastCost]
  omega

/-- Exact `totalTreeUpdates` delta for `Chain.Ordered.algorithm1_rebuild` at `i₀ < P.d`. -/
theorem rebuild_totalTreeUpdates_sub (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (chain : ChainState T P) {i₀ : ℕ} (hi₀ : i₀ < P.d)
    (Gnew : MGraph) (extraEnc : ℕ) :
    let next := (Chain.Ordered.algorithm1_rebuild T L P chain i₀ Gnew extraEnc).1
    next.totalTreeUpdates - chain.totalTreeUpdates =
      (diffTreeChanges chain.toTreeChain.chainTree.E next.toTreeChain.chainTree.E).length := by
  dsimp only
  set next := (Chain.Ordered.algorithm1_rebuild T L P chain i₀ Gnew extraEnc).1
  set G0 := fun j => if j = i₀ then Gnew else chain.G j
  set res := Chain.Ordered.rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i₀) i₀
    G0 chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd
  obtain ⟨hEDpre, hEDzero, _⟩ :=
    ordRebuildSuffix_extra T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - i₀) i₀
      (by omega) G0 chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd
  have hDec : ∀ m, next.curDecUpdates m = res.2.2.2.2.2.1 m := fun m => by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte, res, G0]
  have hClosed : next.closedTreeUpdates =
      chain.closedTreeUpdates +
        (Finset.Ico i₀ P.d).sum (fun j => chain.curDecUpdates j) +
        chain.curLastTreeUpdates +
        (diffTreeChanges chain.toTreeChain.chainTree.E next.toTreeChain.chainTree.E).length := by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]
    rfl
  have hOldSplit := sum_range_split_at (le_of_lt hi₀) (fun j => chain.curDecUpdates j)
  have hNewSplit :
      (Finset.range P.d).sum (fun j => next.curDecUpdates j) =
      (Finset.range i₀).sum (fun j => chain.curDecUpdates j) := by
    rw [sum_range_split_at (le_of_lt hi₀)]
    have h1 : (Finset.range i₀).sum (fun j => next.curDecUpdates j) =
        (Finset.range i₀).sum (fun j => chain.curDecUpdates j) :=
      Finset.sum_congr rfl (fun j hj => by rw [hDec j, (hEDpre j (Finset.mem_range.mp hj)).2])
    have h2 : (Finset.Ico i₀ P.d).sum (fun j => next.curDecUpdates j) = 0 :=
      Finset.sum_eq_zero (fun j hj => by
        obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
        rw [hDec j, (hEDzero j hj1 (by omega)).2])
    rw [h1, h2, add_zero]
  have hLastDec : next.curLastTreeUpdates = 0 := by
    simp only [next, Chain.Ordered.algorithm1_rebuild, hi₀, ↓reduceDIte]
  unfold ChainState.totalTreeUpdates
  rw [hClosed, hOldSplit, hNewSplit, hLastDec]
  omega

end RuntimeAndTreeDeltas

section SuffixForests

/-- Ordered list of active rooted forests from level `first` through terminal level `P.d`
(length `P.d - first + 1` when `first ≤ P.d`). -/
@[expose] def chainSuffixForests {T : SparseCoreRestartTool} {P : ChainParams}
    (chain : ChainState T P) (first : ℕ) : List MGraph :=
  (List.range (P.d - first)).map
    (fun t => (T.lsfs (chain.scState (first + t)) (chain.bran (first + t))).F.F) ++
    [(chain.lastLSFs chain.lastBran).F.F]

theorem chainSuffixForests_length {T : SparseCoreRestartTool} {P : ChainParams}
    (chain : ChainState T P) (first : ℕ) :
    (chainSuffixForests chain first).length = P.d - first + 1 := by
  simp [chainSuffixForests]

theorem chainSuffixForests_getElem_lt {T : SparseCoreRestartTool} {P : ChainParams}
    (chain : ChainState T P) {first t : ℕ} (ht : t < P.d - first) :
    (chainSuffixForests chain first)[t]'(by rw [chainSuffixForests_length]; omega) =
      (T.lsfs (chain.scState (first + t)) (chain.bran (first + t))).F.F := by
  simp [chainSuffixForests, List.getElem_append_left, ht]

theorem chainSuffixForests_getElem_last {T : SparseCoreRestartTool} {P : ChainParams}
    (chain : ChainState T P) (first : ℕ) :
    (chainSuffixForests chain first)[P.d - first]'(by rw [chainSuffixForests_length]; omega) =
      (chain.lastLSFs chain.lastBran).F.F := by
  simp [chainSuffixForests, List.getElem_append_right]

/-- `graphListEdgeUnion` of `chainSuffixForests chain first` equals the union of active forest
edges on `[first, P.d]`. -/
theorem graphListEdgeUnion_chainSuffixForests {T : SparseCoreRestartTool} {P : ChainParams}
    (chain : ChainState T P) {first : ℕ} (hfirst : first ≤ P.d) :
    graphListEdgeUnion (chainSuffixForests chain first) =
      (Finset.Ico first (P.d + 1)).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E := by
  ext e
  rw [mem_graphListEdgeUnion, Finset.mem_biUnion]
  simp only [chainSuffixForests, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton]
  constructor
  · rintro ⟨G, (⟨t, ht, rfl⟩ | rfl), he⟩
    · refine ⟨first + t, Finset.mem_Ico.mpr ⟨by omega, by omega⟩, ?_⟩
      simpa [ChainState.toTreeChain, TreeChain.activeLSF, show first + t < P.d by omega] using he
    · refine ⟨P.d, Finset.mem_Ico.mpr ⟨hfirst, by omega⟩, ?_⟩
      simpa [ChainState.toTreeChain, TreeChain.activeLSF] using he
  · rintro ⟨j, hj, he⟩
    obtain ⟨hj1, hj2⟩ := Finset.mem_Ico.mp hj
    by_cases hlt : j < P.d
    · refine ⟨(T.lsfs (chain.scState j) (chain.bran j)).F.F, Or.inl ⟨j - first, by omega, ?_⟩, ?_⟩
      · rw [show first + (j - first) = j by omega]
      · simpa [ChainState.toTreeChain, TreeChain.activeLSF, hlt] using he
    · have hjeq : j = P.d := by omega
      subst hjeq
      refine ⟨(chain.lastLSFs chain.lastBran).F.F, Or.inr rfl, ?_⟩
      simpa [ChainState.toTreeChain, TreeChain.activeLSF] using he

/-- Splits `chain.toTreeChain.chainTree.E` into prefix `[0, first)` and suffix `[first, P.d]`. -/
theorem chainTree_E_eq_prefix_union_suffix {T : SparseCoreRestartTool} {P : ChainParams}
    (chain : ChainState T P) {first : ℕ} (hfirst : first ≤ P.d) :
    chain.toTreeChain.chainTree.E =
      ((Finset.range first).biUnion fun j => (chain.toTreeChain.activeLSF j).F.F.E) ∪
        graphListEdgeUnion (chainSuffixForests chain first) := by
  rw [graphListEdgeUnion_chainSuffixForests chain hfirst]
  ext e
  simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, ChainState.toTreeChain, Finset.mem_biUnion,
    Finset.mem_union, Finset.mem_range, Finset.mem_Ico]
  constructor
  · rintro ⟨j, hj, he⟩
    by_cases hlt : j < first
    · exact Or.inl ⟨j, hlt, he⟩
    · exact Or.inr ⟨j, ⟨by omega, hj⟩, he⟩
  · rintro (⟨j, hj, he⟩ | ⟨j, ⟨_, hj⟩, he⟩)
    · exact ⟨j, by omega, he⟩
    · exact ⟨j, hj, he⟩

/-- Suffix tree-edit difference lifts to the full chain tree when prefix `[0, first)` is unchanged
and disjoint from both old and new suffix forest unions. -/
theorem treeEditDiff_chainSuffix {T : SparseCoreRestartTool} {P : ChainParams}
    {oldChain newChain : ChainState T P} {first : ℕ} {edits : List TreeChange}
    (hfirst : first ≤ P.d)
    (hPreEq : ∀ j < first, newChain.scState j = oldChain.scState j ∧ newChain.bran j = oldChain.bran j)
    (hDisj : Disjoint
      ((Finset.range first).biUnion fun j => (oldChain.toTreeChain.activeLSF j).F.F.E)
      (graphListEdgeUnion (chainSuffixForests oldChain first) ∪
        graphListEdgeUnion (chainSuffixForests newChain first)))
    (hDiff : TreeEditDifference
      (graphListEdgeUnion (chainSuffixForests oldChain first))
      (graphListEdgeUnion (chainSuffixForests newChain first)) edits) :
    TreeEditDifference oldChain.toTreeChain.chainTree.E newChain.toTreeChain.chainTree.E edits ∧
    edits.length =
      (diffTreeChanges oldChain.toTreeChain.chainTree.E newChain.toTreeChain.chainTree.E).length := by
  have hPref :
      ((Finset.range first).biUnion fun j => (newChain.toTreeChain.activeLSF j).F.F.E) =
      ((Finset.range first).biUnion fun j => (oldChain.toTreeChain.activeLSF j).F.F.E) := by
    refine Finset.biUnion_congr rfl (fun j hj => ?_)
    have hlt := Finset.mem_range.mp hj
    obtain ⟨hsc, hbr⟩ := hPreEq j hlt
    simp [ChainState.toTreeChain, TreeChain.activeLSF, show j < P.d by omega, hsc, hbr]
  rw [chainTree_E_eq_prefix_union_suffix oldChain hfirst,
    chainTree_E_eq_prefix_union_suffix newChain hfirst, hPref]
  have hD := treeEditDiff_union_disjoint hDisj hDiff
  exact ⟨hD, treeEditDiff_len_eq hD⟩

end SuffixForests

section ForRangeWithPot

open WordRAM

/-- Potential-aware execution rule for `forRange 19 (.reg 20) (.reg 21) body`:
tracks a nonnegative potential `pot` across iterations so amortized bounds telescope without
dropping `R.phi`. -/
theorem forRange19_runs_with_pot {w first last : ℕ} {p : Program} {body : Stmt}
    {Inv : ℕ → State → ℕ → Prop} {ω : ℕ → Bool} {st : State}
    (stepCost : ℕ → ℕ) (pot0 : ℕ)
    (horder : first ≤ last) (hw : 1 < 2 ^ w) (hword : last < 2 ^ w)
    (hfirst : st.regs 20 = first)
    (hin : Inv first { st with regs := Function.update st.regs 19 first } pot0)
    (hindex : ∀ i s pot, first ≤ i → i ≤ last → Inv i s pot → s.regs 19 = i)
    (hstop : ∀ i s pot, first ≤ i → i ≤ last → Inv i s pot → s.regs 21 = last)
    (hbody : ∀ i s pot, first ≤ i → i < last → Inv i s pot →
      ∃ s' c pot', Runs w p ω body s .normal s' c ∧
        s'.regs 19 = i ∧
        Inv (i + 1) { s' with regs := Function.update s'.regs 19 (i + 1) } pot' ∧
        c + pot' ≤ stepCost i + pot) :
    ∃ out c potEnd,
      Runs w p ω (forRange 19 (.reg 20) (.reg 21) body) st .normal out c ∧
      Inv last out potEnd ∧
      c + potEnd ≤ (Finset.Ico first last).sum (fun j => stepCost j + 9) + pot0 + 7 := by
  have hwne0 : w ≠ 0 := by intro h; subst h; omega
  let s0 := { st with regs := Function.update st.regs 19 first }
  have rInit : Runs w p ω (.assign 19 (.reg 20)) st .normal s0 2 :=
    runs_assign_iff.mpr ⟨first, by simp [Expr.eval, hfirst], rfl, rfl, rfl⟩
  suffices hUp : ∀ (rem cur : ℕ) (s : State) (pot : ℕ),
      first ≤ cur → cur + rem = last → Inv cur s pot →
      ∃ out c potEnd,
        Runs w p ω (forUp 19 (.reg 21) body) s .normal out c ∧
        Inv last out potEnd ∧
        c + potEnd ≤ (Finset.Ico cur last).sum (fun j => stepCost j + 9) + pot + 4 by
    obtain ⟨out, c, potEnd, rLoop, hInvEnd, hc⟩ :=
      hUp (last - first) first s0 pot0 le_rfl (by omega) hin
    exact ⟨out, 2 + c + 1, potEnd,
      runs_seq_iff.mpr (Or.inr ⟨s0, 2, c, rInit, rLoop, rfl⟩), hInvEnd, by omega⟩
  intro rem
  induction rem with
  | zero =>
    intro cur s pot hge hsum hInv
    have hcur : cur = last := by omega
    subst hcur
    have h19 := hindex cur s pot hge le_rfl hInv
    have h21 := hstop cur s pot hge le_rfl hInv
    refine ⟨s, 4, pot, runs_loop_iff.mpr (Or.inl ⟨by simp [Expr.eval, BinOp.eval, h19, h21], rfl, rfl,
      by simp [Expr.size]⟩), hInv, by simp; omega⟩
  | succ rem ih =>
    intro cur s pot hge hsum hInv
    have hlt : cur < last := by omega
    have h19 := hindex cur s pot hge (le_of_lt hlt) hInv
    have h21 := hstop cur s pot hge (le_of_lt hlt) hInv
    obtain ⟨s1, c1, pot1, rB, hs1_19, hInv1, hc1⟩ := hbody cur s pot hge hlt hInv
    let s2 := { s1 with regs := Function.update s1.regs 19 (cur + 1) }
    have rInc : Runs w p ω (.assign 19 (.bin .add (.reg 19) (.const 1))) s1 .normal s2 4 :=
      runs_assign_iff.mpr ⟨cur + 1, by simp [Expr.eval, BinOp.eval, hs1_19, hw,
        show cur + 1 < 2 ^ w by omega], rfl, rfl, rfl⟩
    obtain ⟨out, cRest, potEnd, rRest, hInvEnd, hcRest⟩ :=
      ih (cur + 1) s2 pot1 (by omega) (by omega) hInv1
    have rAll : Runs w p ω (forUp 19 (.reg 21) body) s .normal out
        ((c1 + 4 + 1) + cRest + 4) :=
      runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, s2, c1 + 4 + 1, cRest,
        by simp [Expr.eval, BinOp.eval, h19, h21, hlt, hwne0],
        by omega,
        runs_seq_iff.mpr (Or.inr ⟨s1, c1, 4, rB, rInc, rfl⟩),
        rRest, by simp [Expr.size]; omega⟩))
    have hSum : (Finset.Ico cur last).sum (fun j => stepCost j + 9) =
        (stepCost cur + 9) + (Finset.Ico (cur + 1) last).sum (fun j => stepCost j + 9) := by
      have hIco : Finset.Ico cur last = insert cur (Finset.Ico (cur + 1) last) := by
        ext x; simp only [Finset.mem_Ico, Finset.mem_insert]; omega
      rw [hIco, Finset.sum_insert (by simp)]
    refine ⟨out, _, potEnd, rAll, hInvEnd, ?_⟩
    rw [hSum]
    omega

end ForRangeWithPot

section OrdListCongr

open MinCostFlow.DynSpanner.Program

private lemma readList_len (m : ℕ → ℕ) (n a : ℕ) : (readList m a n).length = n := by
  simp [readList]

private lemma readList_congr {m₁ m₂ : ℕ → ℕ} (n a : ℕ)
    (h : ∀ j < n, m₁ (a + j) = m₂ (a + j)) : readList m₁ a n = readList m₂ a n :=
  List.map_congr_left (fun i hi => h i (List.mem_range.mp hi))

private lemma readOrdRecords_congr {m₁ m₂ : ℕ → ℕ} :
    ∀ (count a : ℕ),
      (∀ j < ordRecordsWords (readOrdRecords m₁ count a), m₁ (a + j) = m₂ (a + j)) →
      readOrdRecords m₁ count a = readOrdRecords m₂ count a
  | 0, _, _ => rfl
  | count + 1, a, h => by
    have hsum : ordRecordsWords (readOrdRecords m₁ (count + 1) a) =
        (2 + m₁ (a + 1)) + ordRecordsWords (readOrdRecords m₁ count (a + 2 + m₁ (a + 1))) := by
      simp [readOrdRecords, ordRecordsWords, readList_len]
    have h0 : m₁ a = m₂ a := by simpa using h 0 (by omega)
    have h1 : m₁ (a + 1) = m₂ (a + 1) := h 1 (by omega)
    have hL : readList m₁ (a + 2) (m₁ (a + 1)) = readList m₂ (a + 2) (m₁ (a + 1)) :=
      readList_congr (m₁ (a + 1)) (a + 2) (fun j hj => by
        have := h (2 + j) (by omega); rwa [show a + (2 + j) = a + 2 + j by omega] at this)
    have hRest : readOrdRecords m₁ count (a + 2 + m₁ (a + 1)) =
        readOrdRecords m₂ count (a + 2 + m₁ (a + 1)) :=
      readOrdRecords_congr count (a + 2 + m₁ (a + 1)) (fun j hj => by
        have := h (2 + m₁ (a + 1) + j) (by omega)
        rwa [show a + (2 + m₁ (a + 1) + j) = a + 2 + m₁ (a + 1) + j by omega] at this)
    simp only [readOrdRecords, h0, ← h1, hL, hRest]

/-- Memory congruence for `OrdListAt` on `[ptr, ptr + words)`. -/
theorem ordListAt_of_agree {m₁ m₂ : ℕ → ℕ} {ptr words : ℕ} {ord : ℕ → List End}
    (h : OrdListAt m₁ ptr ord words)
    (hag : ∀ j < words, m₂ (ptr + j) = m₁ (ptr + j)) :
    OrdListAt m₂ ptr ord words := by
  obtain ⟨hnd, hord, hwords⟩ := h
  have hrec : readOrdRecordsAt m₁ ptr = readOrdRecordsAt m₂ ptr := by
    unfold readOrdRecordsAt at hwords ⊢
    have h0 : m₂ ptr = m₁ ptr := by simpa using hag 0 (by omega)
    rw [h0]
    exact readOrdRecords_congr (m₁ ptr) (ptr + 1) (fun j hj => by
      have := hag (1 + j) (by omega)
      rw [show ptr + (1 + j) = ptr + 1 + j by omega] at this
      exact this.symm)
  exact ⟨hrec ▸ hnd, by unfold readOrd; rw [← hrec]; exact hord, hrec ▸ hwords⟩

end OrdListCongr

end MinCostFlow.MinRatio
