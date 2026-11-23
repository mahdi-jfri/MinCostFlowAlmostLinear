module

public import MinCostFlow.Chain.BundleRestart
public import MinCostFlow.Chain.Algorithm1

/-!
# Off-Edge Length Agreement for `sparseCoreBundleRestartTool` and `algorithm1_rebuild`

Because `initCompLSF` and `initBundleTree` mask `ℓ₀` to `0` outside `G₀.E` (via `LSF.safeLen`),
`sparseCoreBundleRestartTool.initOrd` and `sparseCoreBundleRestartTool.init` depend only on the
edge lengths on `G.E` and do not depend on the gradient `grad`. Consequently, every level
initialized by `algorithm1_initialize` or rebuilt by `algorithm1_rebuild` agrees with
initializing on the zero-extended live-edge length and gradient tables.
-/

@[expose] public section

namespace MinCostFlow.Chain

open MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.LSF MinCostFlow.Bundle

/-- `initBundleTree` depends only on `ℓ₀` restricted to `G₀.E`. -/
theorem initBundleTree_eq_of_eq_on_E
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (k M N : ℕ) (G₀ : MGraph) {ℓ₀ ℓ₁ : ℕ → ℝ} (h : ∀ a ∈ G₀.E, ℓ₀ a = ℓ₁ a)
    (ord : ℕ → List End) (j : ℕ) :
    initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₀ ord j =
      initBundleTree oracle C_lsst L sparsify k M N G₀ ℓ₁ ord j := by
  classical
  have hsafe := safeLen_eq_of_eq_on_E h
  have hcs := initCompLSF_eq_of_eq_on_E oracle C_lsst G₀ h k j
  dsimp only [initCompLSF] at hcs
  unfold initBundleTree initBundleTreeWith initBundleTreeWithParams
  simp only [hcs, hsafe]

/-- `sparseCoreBundleTool.initOrd` depends only on edge lengths in `G.E` and ignores `grad`. -/
theorem sparseCoreBundleTool_initOrd_eq_of_eq_on_E
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (k M N : ℕ) (G : MGraph) (len len' grad grad' : ℕ → ℝ) (ord : ℕ → List End)
    (h : ∀ e ∈ G.E, len e = len' e) :
    (sparseCoreBundleTool oracle C_lsst L sparsify).initOrd k M N G len grad ord =
      (sparseCoreBundleTool oracle C_lsst L sparsify).initOrd k M N G len' grad' ord := by
  have htr : (fun j => initBundleTree oracle C_lsst L sparsify k M N G len ord j) =
      (fun j => initBundleTree oracle C_lsst L sparsify k M N G len' ord j) :=
    funext fun j => initBundleTree_eq_of_eq_on_E oracle C_lsst L sparsify k M N G h ord j
  dsimp only [initBundleTree, initBundleTreeWith] at htr
  dsimp only [sparseCoreBundleTool, sparseCoreBundleToolWith, initBundleCoreWith,
    initBundleCoreWithParams]
  simp only [htr]

/-- `sparseCoreBundleRestartTool.initOrd` depends only on edge lengths in `G.E` and is
independent of the gradient argument `grad`. -/
theorem sparseCoreBundleRestartTool_initOrd_eq_of_eq_on_E
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (k M N : ℕ) (G : MGraph) (len len' grad grad' : ℕ → ℝ) (ord : ℕ → List End)
    (h : ∀ e ∈ G.E, len e = len' e) :
    (sparseCoreBundleRestartTool oracle C_lsst L sparsify).initOrd k M N G len grad ord =
      (sparseCoreBundleRestartTool oracle C_lsst L sparsify).initOrd k M N G len' grad' ord :=
  sparseCoreBundleTool_initOrd_eq_of_eq_on_E oracle C_lsst L sparsify k M N G len len' grad grad'
    ord h

/-- `sparseCoreBundleRestartTool.initOrd` agrees unconditionally with initializing on the
zero-extended live-edge length and gradient tables. -/
theorem sparseCoreBundleRestartTool_initOrd_eq_zeroExtension
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (k M N : ℕ) (G : MGraph) (len grad : ℕ → ℝ) (ord : ℕ → List End) :
    (sparseCoreBundleRestartTool oracle C_lsst L sparsify).initOrd k M N G len grad ord =
      (sparseCoreBundleRestartTool oracle C_lsst L sparsify).initOrd k M N G
        (fun a => if a ∈ G.E then len a else 0)
        (fun a => if a ∈ G.E then grad a else 0) ord :=
  sparseCoreBundleRestartTool_initOrd_eq_of_eq_on_E oracle C_lsst L sparsify k M N G len _ grad _
    ord (fun e he => by simp [he])

/-- `sparseCoreBundleRestartTool.init` depends only on edge lengths in `G.E` and is independent
of the gradient argument `grad`. -/
theorem sparseCoreBundleRestartTool_init_eq_of_eq_on_E
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (k M N : ℕ) (G : MGraph) (len len' grad grad' : ℕ → ℝ)
    (h : ∀ e ∈ G.E, len e = len' e) :
    (sparseCoreBundleRestartTool oracle C_lsst L sparsify).init k M N G len grad =
      (sparseCoreBundleRestartTool oracle C_lsst L sparsify).init k M N G len' grad' :=
  sparseCoreBundleTool_initOrd_eq_of_eq_on_E oracle C_lsst L sparsify k M N G len len' grad grad'
    (sortedEnds G) h

/-- `sparseCoreBundleRestartTool.init` agrees unconditionally with initializing on the
zero-extended live-edge length and gradient tables. -/
theorem sparseCoreBundleRestartTool_init_eq_zeroExtension
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (k M N : ℕ) (G : MGraph) (len grad : ℕ → ℝ) :
    (sparseCoreBundleRestartTool oracle C_lsst L sparsify).init k M N G len grad =
      (sparseCoreBundleRestartTool oracle C_lsst L sparsify).init k M N G
        (fun a => if a ∈ G.E then len a else 0)
        (fun a => if a ∈ G.E then grad a else 0) :=
  sparseCoreBundleRestartTool_init_eq_of_eq_on_E oracle C_lsst L sparsify k M N G len _ grad _
    (fun e he => by simp [he])

private lemma bundleTreeChain_chainLen_congr {C₁ C₂ : TreeChain} {ℓ : ℕ → ℝ} {i : ℕ}
    (hLSF : ∀ m < i, C₁.activeLSF m = C₂.activeLSF m) :
    C₁.chainLen ℓ i = C₂.chainLen ℓ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    dsimp only [TreeChain.chainLen]
    rw [ih (fun m hm => hLSF m (Nat.lt_succ_of_lt hm)), hLSF i (Nat.lt_succ_self i)]

private lemma bundleTreeChain_chainGrad_congr {C₁ C₂ : TreeChain} {g : ℕ → ℝ} {i : ℕ}
    (hG : ∀ m < i, C₁.G m = C₂.G m)
    (hLSF : ∀ m < i, C₁.activeLSF m = C₂.activeLSF m) :
    C₁.chainGrad g i = C₂.chainGrad g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    dsimp only [TreeChain.chainGrad]
    rw [ih (fun m hm => hG m (Nat.lt_succ_of_lt hm)) (fun m hm => hLSF m (Nat.lt_succ_of_lt hm)),
      hG i (Nat.lt_succ_self i), hLSF i (Nat.lt_succ_self i)]

private lemma bundleRebuildSuffix_prefix_and_coreAt (T : SparseCoreRestartTool)
    (L : LastLevelTool) (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ), idx + rem ≤ P.d →
      ∀ (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      let res := rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      let G' := res.1
      let sc' := res.2.1
      let bran' := res.2.2.1
      (∀ m ≤ idx, G' m = G m) ∧
      (∀ m < idx, sc' m = sc m ∧ bran' m = bran m) ∧
      (∀ j, idx ≤ j → j < idx + rem →
        let Cfin : TreeChain :=
          { d := P.d, k := P.k, G := G', lsfs := fun m => T.lsfs (sc' m), bran := bran',
            S := fun m => T.S (sc' m), emb := fun m => T.emb (sc' m),
            lastK := 1, lastLSFs := fun _ => ⟨G' j, ⟨G' j, ∅⟩, fun _ => 1⟩, lastBran := 0 }
        sc' j = T.init P.k (lvlM j) N₀ (G' j) (Cfin.chainLen ℓ₀ j) (Cfin.chainGrad g₀ j) ∧
        G' (j + 1) = T.S (sc' j) 0 ∧
        bran' j = 0) := by
  intro rem
  induction rem with
  | zero =>
    intro idx _ G sc bran upd cEnc cDec cFwd
    refine ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl⟩, fun j hj1 hj2 => by omega⟩
  | succ rem ih =>
    intro idx hbound G sc bran upd cEnc cDec cFwd
    dsimp only [rebuildSuffix]
    let Cstep : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    let ℓi := Cstep.chainLen ℓ₀ idx
    let gi := Cstep.chainGrad g₀ idx
    let sc_i := T.init P.k (lvlM idx) N₀ (G idx) ℓi gi
    let G1 := fun j => if j = idx + 1 then T.S sc_i 0 else G j
    let sc1 := fun j => if j = idx then sc_i else sc j
    let bran1 := fun j => if j = idx then 0 else bran j
    let upd1 := fun j => if j = idx then 0 else upd j
    let cEnc1 := fun j => if j = idx then 0 else cEnc j
    let cDec1 := fun j => if j = idx then 0 else cDec j
    let cFwd1 := fun j => if j = idx then 0 else cFwd j
    obtain ⟨hG_rec, hSB_rec, hCore_rec⟩ :=
      ih (idx + 1) (by omega) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1
    refine ⟨?_, ?_, ?_⟩
    · intro m hm
      rw [hG_rec m (Nat.le_succ_of_le hm)]
      dsimp only [G1]
      simp only [show m ≠ idx + 1 by omega, ↓reduceIte]
    · intro m hm
      have ⟨hsc, hbr⟩ := hSB_rec m (Nat.lt_succ_of_lt hm)
      dsimp only [sc1, bran1] at hsc hbr
      simp only [show m ≠ idx by omega, ↓reduceIte] at hsc hbr
      exact ⟨hsc, hbr⟩
    · intro j hj1 hj2
      by_cases hjeq : j = idx
      · subst hjeq
        have hGj : (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1 j =
            G j := by
          rw [hG_rec j (Nat.le_succ j)]; dsimp only [G1]
          simp only [show j ≠ j + 1 by omega, ↓reduceIte]
        have hGj1 : (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1
            (j + 1) = T.S sc_i 0 := by
          rw [hG_rec (j + 1) le_rfl]; dsimp only [G1]; simp only [↓reduceIte]
        have ⟨hscj, hbrj⟩ := hSB_rec j (Nat.lt_succ_self j)
        dsimp only [sc1, bran1] at hscj hbrj
        simp only [↓reduceIte] at hscj hbrj
        have hGm : ∀ m < j,
            (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1 m =
              G m := fun m hm => by
          rw [hG_rec m (by omega)]; dsimp only [G1]
          simp only [show m ≠ j + 1 by omega, ↓reduceIte]
        have hLSFm : ∀ m < j,
            T.lsfs ((rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.1 m)
              ((rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.1 m) =
            T.lsfs (sc m) (bran m) := fun m hm => by
          have ⟨h1, h2⟩ := hSB_rec m (by omega)
          dsimp only [sc1, bran1] at h1 h2
          simp only [show m ≠ j by omega, ↓reduceIte] at h1 h2
          rw [h1, h2]
        have hlen_eq :
            ({ d := P.d, k := P.k,
               G := (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1,
               lsfs := fun m => T.lsfs
                 ((rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.1 m),
               bran := (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.1,
               S := fun m => T.S
                 ((rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.1 m),
               emb := fun m => T.emb
                 ((rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.1 m),
               lastK := 1,
               lastLSFs := fun _ =>
                 ⟨(rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1 j,
                  ⟨(rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1 j, ∅⟩,
                  fun _ => 1⟩,
               lastBran := 0 } : TreeChain).chainLen ℓ₀ j = ℓi :=
          bundleTreeChain_chainLen_congr (fun m hm => by
            dsimp only [TreeChain.activeLSF, Cstep]
            simp only [show m < P.d by omega, ↓reduceIte]
            exact hLSFm m hm)
        have hgrad_eq :
            ({ d := P.d, k := P.k,
               G := (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1,
               lsfs := fun m => T.lsfs
                 ((rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.1 m),
               bran := (rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.2.1,
               S := fun m => T.S
                 ((rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.1 m),
               emb := fun m => T.emb
                 ((rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).2.1 m),
               lastK := 1,
               lastLSFs := fun _ =>
                 ⟨(rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1 j,
                  ⟨(rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1) G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1).1 j, ∅⟩,
                  fun _ => 1⟩,
               lastBran := 0 } : TreeChain).chainGrad g₀ j = gi :=
          bundleTreeChain_chainGrad_congr (fun m hm => hGm m hm) (fun m hm => by
            dsimp only [TreeChain.activeLSF, Cstep]
            simp only [show m < P.d by omega, ↓reduceIte]
            exact hLSFm m hm)
        refine ⟨?_, ?_, hbrj⟩
        · rw [hlen_eq, hgrad_eq, hscj, hGj]
        · rw [hGj1, hscj]
      · exact hCore_rec j (by omega) (by omega)

/-- At every rebuilt level `first ≤ level < P.d`, `algorithm1_rebuild` sets `next.scState level`
to `T.init P.k (chain.lvlM level) chain.N₀ (next.G level) (next.toTreeChain.chainLen chain.ℓ level) (next.toTreeChain.chainGrad chain.g level)`. -/
theorem algorithm1_rebuild_bundleCoreAt_eq
    (T : SparseCoreRestartTool) (L : LastLevelTool) (P : ChainParams)
    (chain : ChainState T P) (first level : ℕ) (hfirst : first ≤ level) (hlevel : level < P.d)
    (Gnew : MGraph) (enc : ℕ) :
    let next := (algorithm1_rebuild T L P chain first Gnew enc).1
    next.scState level = T.init P.k (chain.lvlM level) chain.N₀ (next.G level)
      (next.toTreeChain.chainLen chain.ℓ level) (next.toTreeChain.chainGrad chain.g level) := by
  dsimp only [algorithm1_rebuild]
  have hfi : first < P.d := lt_of_le_of_lt hfirst hlevel
  simp only [hfi, ↓reduceDIte]
  let res := rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - first) first
    (fun j => if j = first then Gnew else chain.G j)
    chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd
  have hcore := (bundleRebuildSuffix_prefix_and_coreAt T L P chain.lvlM chain.N₀ chain.ℓ chain.g
    (P.d - first) first (by omega) (fun j => if j = first then Gnew else chain.G j)
    chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd).2.2
    level hfirst (by omega)
  have hlen :
      ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
         bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
         lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2,
         lastBran := 0 } : TreeChain).chainLen chain.ℓ level =
      ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
         bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
         lastK := 1, lastLSFs := fun _ => ⟨res.1 level, ⟨res.1 level, ∅⟩, fun _ => 1⟩,
         lastBran := 0 } : TreeChain).chainLen chain.ℓ level :=
    bundleTreeChain_chainLen_congr (fun m hm => by
      dsimp only [TreeChain.activeLSF]
      simp only [lt_trans hm hlevel, ↓reduceIte])
  have hgrad :
      ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
         bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
         lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2,
         lastBran := 0 } : TreeChain).chainGrad chain.g level =
      ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
         bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
         lastK := 1, lastLSFs := fun _ => ⟨res.1 level, ⟨res.1 level, ∅⟩, fun _ => 1⟩,
         lastBran := 0 } : TreeChain).chainGrad chain.g level :=
    bundleTreeChain_chainGrad_congr (fun _ _ => rfl) (fun m hm => by
      dsimp only [TreeChain.activeLSF]
      simp only [lt_trans hm hlevel, ↓reduceIte])
  dsimp only [ChainState.toTreeChain]
  change res.2.1 level = T.init P.k (chain.lvlM level) chain.N₀ (res.1 level) _ _
  rw [hlen, hgrad]
  exact hcore.1

/-- Every level `first ≤ level < P.d` rebuilt by `algorithm1_rebuild` with
`sparseCoreBundleRestartTool` agrees unconditionally with initializing on the zero-extended
live-edge length and gradient tables. -/
theorem algorithm1_rebuild_bundleCoreAt_eq_zeroExtension
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (L : LastLevelTool) (P : ChainParams)
    (chain : ChainState (sparseCoreBundleRestartTool oracle C depth sparsify) P)
    (first level : ℕ) (hfirst : first ≤ level) (hlevel : level < P.d)
    (Gnew : MGraph) (enc : ℕ) :
    let T := sparseCoreBundleRestartTool oracle C depth sparsify
    let next := (algorithm1_rebuild T L P chain first Gnew enc).1
    let G := next.G level
    let len := next.toTreeChain.chainLen chain.ℓ level
    let grad := next.toTreeChain.chainGrad chain.g level
    next.scState level = T.init P.k (chain.lvlM level) chain.N₀ G
      (fun a => if a ∈ G.E then len a else 0) (fun a => if a ∈ G.E then grad a else 0) := by
  dsimp only
  rw [algorithm1_rebuild_bundleCoreAt_eq _ L P chain first level hfirst hlevel Gnew enc]
  exact sparseCoreBundleRestartTool_init_eq_zeroExtension oracle C depth sparsify P.k
    (chain.lvlM level) chain.N₀ _ _ _

/-- For every rebuilt level `level = j + 1 < P.d` with `first ≤ j`, the rebuilt bundle sparse-core
state equals initializing on the zero-extended live-edge length and gradient tables. -/
theorem algorithm1_rebuild_bundleNextCore_eq_zeroExtension
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (L : LastLevelTool) (P : ChainParams)
    (chain : ChainState (sparseCoreBundleRestartTool oracle C depth sparsify) P)
    (first j : ℕ) (hfirst : first ≤ j) (hj : j + 1 < P.d)
    (Gnew : MGraph) (enc : ℕ) :
    let T := sparseCoreBundleRestartTool oracle C depth sparsify
    let next := (algorithm1_rebuild T L P chain first Gnew enc).1
    let level := j + 1
    let G := next.G level
    let len := next.toTreeChain.chainLen chain.ℓ level
    let grad := next.toTreeChain.chainGrad chain.g level
    next.scState level = T.init P.k (chain.lvlM level) chain.N₀ G
      (fun a => if a ∈ G.E then len a else 0) (fun a => if a ∈ G.E then grad a else 0) :=
  algorithm1_rebuild_bundleCoreAt_eq_zeroExtension oracle C depth sparsify L P chain first (j + 1)
    (hfirst.trans (Nat.le_succ j)) hj Gnew enc

/-- Every level `level < P.d` initialized by `algorithm1_initialize` with
`sparseCoreBundleRestartTool` agrees unconditionally with initializing on the zero-extended
live-edge length and gradient tables. -/
theorem algorithm1_initialize_bundleCoreAt_eq_zeroExtension
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C : ℝ) (depth : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)
    (L : LastLevelTool) (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ)
    (G₀ : MGraph) (len₀ grad₀ : ℕ → ℝ) (level : ℕ) (hlevel : level < P.d) :
    let T := sparseCoreBundleRestartTool oracle C depth sparsify
    let next := (algorithm1_initialize T L P lvlM N₀ G₀ len₀ grad₀).1
    let G := next.G level
    let len := next.toTreeChain.chainLen len₀ level
    let grad := next.toTreeChain.chainGrad grad₀ level
    next.scState level = T.init P.k (lvlM level) N₀ G
      (fun a => if a ∈ G.E then len a else 0) (fun a => if a ∈ G.E then grad a else 0) := by
  let T := sparseCoreBundleRestartTool oracle C depth sparsify
  let res := rebuildSuffix T L P lvlM N₀ len₀ grad₀ P.d 0
    (fun _ => G₀) (fun _ => T.init P.k (lvlM 0) N₀ G₀ len₀ grad₀) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0)
  have hcore := (bundleRebuildSuffix_prefix_and_coreAt T L P lvlM N₀ len₀ grad₀ P.d 0 (by omega)
    (fun _ => G₀) (fun _ => T.init P.k (lvlM 0) N₀ G₀ len₀ grad₀) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) (fun _ => 0) (fun _ => 0)).2.2 level (Nat.zero_le level) (by omega)
  have hlen :
      ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
         bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
         lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2,
         lastBran := 0 } : TreeChain).chainLen len₀ level =
      ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
         bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
         lastK := 1, lastLSFs := fun _ => ⟨res.1 level, ⟨res.1 level, ∅⟩, fun _ => 1⟩,
         lastBran := 0 } : TreeChain).chainLen len₀ level :=
    bundleTreeChain_chainLen_congr (fun m hm => by
      dsimp only [TreeChain.activeLSF]
      simp only [lt_trans hm hlevel, ↓reduceIte])
  have hgrad :
      ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
         bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
         lastK := res.2.2.2.2.2.2.2.1.1, lastLSFs := res.2.2.2.2.2.2.2.1.2,
         lastBran := 0 } : TreeChain).chainGrad grad₀ level =
      ({ d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
         bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
         lastK := 1, lastLSFs := fun _ => ⟨res.1 level, ⟨res.1 level, ∅⟩, fun _ => 1⟩,
         lastBran := 0 } : TreeChain).chainGrad grad₀ level :=
    bundleTreeChain_chainGrad_congr (fun _ _ => rfl) (fun m hm => by
      dsimp only [TreeChain.activeLSF]
      simp only [lt_trans hm hlevel, ↓reduceIte])
  have hinit :
      (algorithm1_initialize T L P lvlM N₀ G₀ len₀ grad₀).1.scState level =
        T.init P.k (lvlM level) N₀ ((algorithm1_initialize T L P lvlM N₀ G₀ len₀ grad₀).1.G level)
          ((algorithm1_initialize T L P lvlM N₀ G₀ len₀ grad₀).1.toTreeChain.chainLen len₀ level)
          ((algorithm1_initialize T L P lvlM N₀ G₀ len₀ grad₀).1.toTreeChain.chainGrad grad₀ level) := by
    dsimp only [algorithm1_initialize, ChainState.toTreeChain]
    change res.2.1 level = T.init P.k (lvlM level) N₀ (res.1 level) _ _
    rw [hlen, hgrad]
    exact hcore.1
  dsimp only
  rw [hinit]
  exact sparseCoreBundleRestartTool_init_eq_zeroExtension oracle C depth sparsify P.k (lvlM level)
    N₀ _ _ _

end MinCostFlow.Chain

end
