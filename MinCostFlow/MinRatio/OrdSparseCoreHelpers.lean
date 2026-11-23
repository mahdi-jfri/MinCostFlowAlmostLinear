module

public import MinCostFlow.SparseCore.Program.Contract
public import MinCostFlow.Chain.Ordered.Algorithm1
public import MinCostFlow.Chain.BundleRestartInitAgree

/-!
# Ordered sparse-core machine contract helpers and exact suffix agreement

Bridges `SparseCore.Program.sparseCoreOrdMachineContract` with the ordered Algorithm 1 model
(`Chain.Ordered.Algorithm1`):
1. `chainLevelOrdAbs`: extracts the `SparseCoreOrdAbs T` abstract state
   `(scState i, G i, levelOrd i, updCount i)` of level `i` from a `ChainState T P`.
2. Contract state and input preservation lemmas (`sparseCoreOrdMachineContract_init_input`,
   `_initPre_of_tables`, `_init_model`, `_update_input`, `_restart_input`, `_readout_state`).
3. `ToolInitOrdEqOnE`: exact off-edge length/gradient independence of `T.initOrd` (discharged for
   `sparseCoreBundleRestartTool` by `sparseCoreBundleRestartTool_initOrd_eq_of_eq_on_E`).
4. Exact level-by-level core-state, branch, update-count, and zero-extension agreement for
   `Chain.Ordered.rebuildSuffix`, `Chain.Ordered.algorithm1_initialize`,
   `Chain.Ordered.algorithm1_rebuild`, and `Chain.Ordered.algorithm1_shift`.
5. Telescoping sum lemma `ordCoreCost_telescope` for cumulative `T.cost` budgets.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program

/-- The `SparseCoreOrdAbs` abstract state carried at nonterminal level `i` of a `ChainState`
for the ordered chain: `(scState i, G i, levelOrd i, updCount i)`. -/
@[expose] def chainLevelOrdAbs {T : SparseCoreRestartTool} {P : ChainParams}
    (chain : ChainState T P) (i : ℕ) : SparseCoreOrdAbs T :=
  ⟨chain.scState i, chain.G i, chain.levelOrd i, chain.updCount i⟩

/-- `T.initOrd` depends only on edge lengths on `G.E` and is independent of the gradient argument.
Holds for `sparseCoreBundleRestartTool` (`sparseCoreBundleRestartTool_initOrdEqOnE`). -/
@[expose] def ToolInitOrdEqOnE (T : SparseCoreRestartTool) : Prop :=
  ∀ (k M N : ℕ) (G : MGraph) (len len' grad grad' : ℕ → ℝ) (ord : ℕ → List End),
    (∀ e ∈ G.E, len e = len' e) →
    T.initOrd k M N G len grad ord = T.initOrd k M N G len' grad' ord

theorem sparseCoreBundleRestartTool_initOrdEqOnE
    (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ) (L : ℕ)
    (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut) :
    ToolInitOrdEqOnE (sparseCoreBundleRestartTool oracle C_lsst L sparsify) :=
  fun k M N G len len' grad grad' ord h =>
    sparseCoreBundleRestartTool_initOrd_eq_of_eq_on_E oracle C_lsst L sparsify k M N G
      len len' grad grad' ord h

section ContractHelpers

variable {w L k M N vCap eCap : ℕ} {fmt : Num.Format w}
variable {tool : SparseCoreRestartTool} {initialGraph : MGraph}
variable {P : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}

/-- Initialization of `sparseCoreOrdMachineContract` establishes `SparseCoreOrdInput`. -/
theorem sparseCoreOrdMachineContract_init_input {args : List ℕ} {mem mem' : ℕ → ℕ}
    {a : SparseCoreOrdAbs tool}
    (hpre : (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation).initPre
      args mem)
    (hpost : (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation).initPost
      args mem a mem') :
    SparseCoreOrdInput tool k M N a.st a.G a.ord a.n := by
  obtain ⟨graph, lengths, gradient, ord, heap, rfl, _, _, _, hval, hm, hn, _, _, _, _, _, _,
    hrot, _, hpos⟩ := hpre
  subst hpost
  exact SparseCoreOrdInput.init initialGraph
    (readEdgeValues mem lengths fmt.limbBits L fmt.precision initialGraph.E)
    (readEdgeValues mem gradient fmt.limbBits L fmt.precision initialGraph.E)
    (readOrd mem ord) hval hm hn hpos hrot

/-- Build `sparseCoreOrdMachineContract.initPre` from graph, value tables, and `OrdListAt`. -/
theorem sparseCoreOrdMachineContract_initPre_of_tables {graph lengths gradient ord heap : ℕ}
    {mem : ℕ → ℕ} {ℓ g : ℕ → ℝ} {ordFn : ℕ → List End} {ordWords : ℕ}
    (hk : 0 < k) (hword : (M + N + 2) ^ P.wordExp < 2 ^ w)
    (hg : DynGraphAt mem graph vCap eCap initialGraph)
    (hm : initialGraph.m ≤ M) (hn : initialGraph.n ≤ N)
    (hgb : graph + dynGraphSize vCap eCap ≤ heap)
    (hlb : lengths + eCap * L ≤ heap) (hgrb : gradient + eCap * L ≤ heap)
    (hord : OrdListAt mem ord ordFn ordWords)
    (hordb : ord + ordWords ≤ heap)
    (hordW : ∀ j < ordWords, mem (ord + j) < 2 ^ w)
    (hrot : IsRotationOrder initialGraph ordFn)
    (hℓ : EdgeValuesAt mem lengths fmt.limbBits L fmt.precision initialGraph.E ℓ)
    (hgv : EdgeValuesAt mem gradient fmt.limbBits L fmt.precision initialGraph.E g)
    (hpos : ∀ e ∈ initialGraph.E, 0 < ℓ e) :
    (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation).initPre
      [graph, lengths, gradient, ord, heap] mem := by
  have hordWordsEq : ordListWords mem ord = ordWords := hord.2.2.symm
  have hreadOrd : readOrd mem ord = ordFn := hord.2.1
  refine ⟨graph, lengths, gradient, ord, heap, rfl, hk, hword, hg, hg.1, hm, hn,
    hgb, hlb, hgrb, ?_, hordWordsEq.symm ▸ hordb, hordWordsEq.symm ▸ hordW,
    hreadOrd.symm ▸ hrot, fun e he => ⟨hg.2.2.1 e he, (hℓ e he).1, (hgv e he).1⟩,
    fun e he => ?_⟩
  · exact ⟨hord.1, rfl, rfl⟩
  · simp only [readEdgeValues, he, ↓reduceIte, (hℓ e he).2]; exact hpos e he

/-- `initPost` of `sparseCoreOrdMachineContract` produces the exact zero-extended `initOrd` state. -/
theorem sparseCoreOrdMachineContract_init_model {graph lengths gradient ord heap : ℕ}
    {mem mem' : ℕ → ℕ} {ℓ g : ℕ → ℝ} {ordFn : ℕ → List End} {ordWords : ℕ}
    {a : SparseCoreOrdAbs tool}
    (hord : OrdListAt mem ord ordFn ordWords)
    (hℓ : EdgeValuesAt mem lengths fmt.limbBits L fmt.precision initialGraph.E ℓ)
    (hgv : EdgeValuesAt mem gradient fmt.limbBits L fmt.precision initialGraph.E g)
    (hpost : (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation).initPost
      [graph, lengths, gradient, ord, heap] mem a mem') :
    a = ⟨tool.initOrd k M N initialGraph
          (fun e => if e ∈ initialGraph.E then ℓ e else 0)
          (fun e => if e ∈ initialGraph.E then g e else 0) ordFn,
        initialGraph, ordFn, 0⟩ := by
  have h1 : readEdgeValues mem lengths fmt.limbBits L fmt.precision initialGraph.E =
      fun e => if e ∈ initialGraph.E then ℓ e else 0 := by
    funext e
    by_cases he : e ∈ initialGraph.E
    · simp only [readEdgeValues, he, ↓reduceIte, (hℓ e he).2]
    · simp [readEdgeValues, he]
  have h2 : readEdgeValues mem gradient fmt.limbBits L fmt.precision initialGraph.E =
      fun e => if e ∈ initialGraph.E then g e else 0 := by
    funext e
    by_cases he : e ∈ initialGraph.E
    · simp only [readEdgeValues, he, ↓reduceIte, (hgv e he).2]
    · simp [readEdgeValues, he]
  simpa [sparseCoreOrdMachineContract, h1, h2, hord.2.1] using hpost

/-- Update (op 0) of `sparseCoreOrdMachineContract` preserves `SparseCoreOrdInput`. -/
theorem sparseCoreOrdMachineContract_update_input {args : List ℕ} {mem mem' : ℕ → ℕ}
    {a a' : SparseCoreOrdAbs tool}
    (hpre : (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation).pre
      0 a args mem)
    (hpost : (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation).post
      0 a args mem a' mem') :
    SparseCoreOrdInput tool k M N a'.st a'.G a'.ord a'.n := by
  obtain ⟨handle, graph, batch, words, edits, editWords, lengths, gradient, heap, rfl,
    hin, _, _, hval, _, _, hordB, hthr, _, _, _, _, _, _, _, _, hpos⟩ := hpre
  rw [hpost.1]
  exact SparseCoreOrdInput.update hin _ _ _ _ hval hpos hordB hthr

/-- Restart (op 1) of `sparseCoreOrdMachineContract` preserves `SparseCoreOrdInput`. -/
theorem sparseCoreOrdMachineContract_restart_input {args : List ℕ} {mem mem' : ℕ → ℕ}
    {a a' : SparseCoreOrdAbs tool}
    (hpre : (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation).pre
      1 a args mem)
    (hpost : (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation).post
      1 a args mem a' mem') :
    SparseCoreOrdInput tool k M N a'.st a'.G a'.ord a'.n := by
  obtain ⟨hin, handle, branch, heap, rfl, hbr⟩ := hpre
  rw [hpost]
  exact SparseCoreOrdInput.restart hin branch hbr

/-- Readouts (ops 2, 3, 4, 5) leave the `SparseCoreOrdAbs` abstract state unchanged. -/
theorem sparseCoreOrdMachineContract_readout_state {op : ℕ} {args : List ℕ} {mem mem' : ℕ → ℕ}
    {a a' : SparseCoreOrdAbs tool} (hop : op = 2 ∨ op = 3 ∨ op = 4 ∨ op = 5)
    (hpost : (sparseCoreOrdMachineContract fmt L tool initialGraph k M N vCap eCap P allocation).post
      op a args mem a' mem') :
    a' = a := by
  rcases hop with rfl | rfl | rfl | rfl <;> exact hpost.1

end ContractHelpers

section OrderedSuffixAgreement

private lemma ordTreeChain_chainLen_congr {C₁ C₂ : TreeChain} {ℓ : ℕ → ℝ} {i : ℕ}
    (hLSF : ∀ m < i, C₁.activeLSF m = C₂.activeLSF m) :
    C₁.chainLen ℓ i = C₂.chainLen ℓ i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    dsimp only [TreeChain.chainLen]
    rw [ih (fun m hm => hLSF m (Nat.lt_succ_of_lt hm)), hLSF i (Nat.lt_succ_self i)]

private lemma ordTreeChain_chainGrad_congr {C₁ C₂ : TreeChain} {g : ℕ → ℝ} {i : ℕ}
    (hG : ∀ m < i, C₁.G m = C₂.G m)
    (hLSF : ∀ m < i, C₁.activeLSF m = C₂.activeLSF m) :
    C₁.chainGrad g i = C₂.chainGrad g i := by
  induction i with
  | zero => rfl
  | succ i ih =>
    dsimp only [TreeChain.chainGrad]
    rw [ih (fun m hm => hG m (Nat.lt_succ_of_lt hm)) (fun m hm => hLSF m (Nat.lt_succ_of_lt hm)),
      hG i (Nat.lt_succ_self i), hLSF i (Nat.lt_succ_self i)]

/-- Exact level-by-level characterization of `Chain.Ordered.rebuildSuffix`:
preserves prefix `G m` (`m ≤ idx`) and `(sc m, bran m, upd m)` (`m < idx`), and for every
`j ∈ [idx, idx + rem)` sets `sc' j = T.initOrd P.k (lvlM j) N₀ (G' j) (chainLen ℓ₀ j)
(chainGrad g₀ j) (chainLevelOrd T G' sc' bran' j)`, `G' (j + 1) = T.S (sc' j) 0`, `bran' j = 0`,
and `upd' j = 0`. -/
theorem ordRebuildSuffix_prefix_and_coreAt (T : SparseCoreRestartTool)
    (L : LastLevelTool) (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) :
    ∀ (rem idx : ℕ), idx + rem ≤ P.d →
      ∀ (G : ℕ → MGraph) (sc : ℕ → T.State) (bran upd cEnc cDec cFwd : ℕ → ℕ),
      let res := Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem idx G sc bran upd cEnc cDec cFwd
      let G' := res.1
      let sc' := res.2.1
      let bran' := res.2.2.1
      let upd' := res.2.2.2.1
      (∀ m ≤ idx, G' m = G m) ∧
      (∀ m < idx, sc' m = sc m ∧ bran' m = bran m ∧ upd' m = upd m) ∧
      (∀ j, idx ≤ j → j < idx + rem →
        let Cfin : TreeChain :=
          { d := P.d, k := P.k, G := G', lsfs := fun m => T.lsfs (sc' m), bran := bran',
            S := fun m => T.S (sc' m), emb := fun m => T.emb (sc' m),
            lastK := 1, lastLSFs := fun _ => ⟨G' j, ⟨G' j, ∅⟩, fun _ => 1⟩, lastBran := 0 }
        sc' j = T.initOrd P.k (lvlM j) N₀ (G' j) (Cfin.chainLen ℓ₀ j) (Cfin.chainGrad g₀ j)
          (Chain.Ordered.chainLevelOrd T G' sc' bran' j) ∧
        G' (j + 1) = T.S (sc' j) 0 ∧
        bran' j = 0 ∧
        upd' j = 0) := by
  intro rem
  induction rem with
  | zero =>
    intro idx _ G sc bran upd cEnc cDec cFwd
    refine ⟨fun _ _ => rfl, fun _ _ => ⟨rfl, rfl, rfl⟩, fun j hj1 hj2 => by omega⟩
  | succ rem ih =>
    intro idx hbound G sc bran upd cEnc cDec cFwd
    dsimp only [Chain.Ordered.rebuildSuffix]
    let Cstep : TreeChain :=
      { d := P.d, k := P.k, G := G, lsfs := fun j => T.lsfs (sc j), bran := bran,
        S := fun j => T.S (sc j), emb := fun j => T.emb (sc j),
        lastK := 1, lastLSFs := fun _ => ⟨G idx, ⟨G idx, ∅⟩, fun _ => 1⟩, lastBran := 0 }
    let ℓi := Cstep.chainLen ℓ₀ idx
    let gi := Cstep.chainGrad g₀ idx
    let sc_i := T.initOrd P.k (lvlM idx) N₀ (G idx) ℓi gi
      (Chain.Ordered.chainLevelOrd T G sc bran idx)
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
      dsimp only [G1]; simp only [show m ≠ idx + 1 by omega, ↓reduceIte]
    · intro m hm
      obtain ⟨hsc, hbr, hup⟩ := hSB_rec m (Nat.lt_succ_of_lt hm)
      dsimp only [sc1, bran1, upd1] at hsc hbr hup
      simp only [show m ≠ idx by omega, ↓reduceIte] at hsc hbr hup
      exact ⟨hsc, hbr, hup⟩
    · intro j hj1 hj2
      by_cases hjeq : j = idx
      · subst hjeq
        let resR := Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem (j + 1)
          G1 sc1 bran1 upd1 cEnc1 cDec1 cFwd1
        have hGj : resR.1 j = G j := by
          rw [hG_rec j (Nat.le_succ j)]; dsimp only [G1]
          simp only [show j ≠ j + 1 by omega, ↓reduceIte]
        have hGj1 : resR.1 (j + 1) = T.S sc_i 0 := by
          rw [hG_rec (j + 1) le_rfl]; dsimp only [G1]; simp only [↓reduceIte]
        obtain ⟨hscj, hbrj, hupj⟩ := hSB_rec j (Nat.lt_succ_self j)
        dsimp only [sc1, bran1, upd1] at hscj hbrj hupj
        simp only [↓reduceIte] at hscj hbrj hupj
        have hGm : ∀ m < j, resR.1 m = G m := fun m hm => by
          rw [hG_rec m (by omega)]; dsimp only [G1]
          simp only [show m ≠ j + 1 by omega, ↓reduceIte]
        have hSCm : ∀ m < j, resR.2.1 m = sc m ∧ resR.2.2.1 m = bran m := fun m hm => by
          obtain ⟨h1, h2, _⟩ := hSB_rec m (by omega)
          dsimp only [sc1, bran1] at h1 h2
          simp only [show m ≠ j by omega, ↓reduceIte] at h1 h2
          exact ⟨h1, h2⟩
        have hOrdEq : Chain.Ordered.chainLevelOrd T resR.1 resR.2.1 resR.2.2.1 j =
            Chain.Ordered.chainLevelOrd T G sc bran j := by
          unfold Chain.Ordered.chainLevelOrd
          split_ifs with hj0
          · subst hj0; rw [hGj]
          · have hlt : j - 1 < j := by omega
            obtain ⟨h1, h2⟩ := hSCm (j - 1) hlt
            rw [h1, h2]
        have hlen_eq :
            ({ d := P.d, k := P.k, G := resR.1, lsfs := fun m => T.lsfs (resR.2.1 m),
               bran := resR.2.2.1, S := fun m => T.S (resR.2.1 m), emb := fun m => T.emb (resR.2.1 m),
               lastK := 1, lastLSFs := fun _ => ⟨resR.1 j, ⟨resR.1 j, ∅⟩, fun _ => 1⟩,
               lastBran := 0 } : TreeChain).chainLen ℓ₀ j = ℓi :=
          ordTreeChain_chainLen_congr (fun m hm => by
            dsimp only [TreeChain.activeLSF, Cstep]
            simp only [show m < P.d by omega, ↓reduceIte]
            obtain ⟨h1, h2⟩ := hSCm m hm; rw [h1, h2])
        have hgrad_eq :
            ({ d := P.d, k := P.k, G := resR.1, lsfs := fun m => T.lsfs (resR.2.1 m),
               bran := resR.2.2.1, S := fun m => T.S (resR.2.1 m), emb := fun m => T.emb (resR.2.1 m),
               lastK := 1, lastLSFs := fun _ => ⟨resR.1 j, ⟨resR.1 j, ∅⟩, fun _ => 1⟩,
               lastBran := 0 } : TreeChain).chainGrad g₀ j = gi :=
          ordTreeChain_chainGrad_congr (fun m hm => hGm m hm) (fun m hm => by
            dsimp only [TreeChain.activeLSF, Cstep]
            simp only [show m < P.d by omega, ↓reduceIte]
            obtain ⟨h1, h2⟩ := hSCm m hm; rw [h1, h2])
        refine ⟨?_, ?_, hbrj, hupj⟩
        · change resR.2.1 j = _
          rw [hlen_eq, hgrad_eq, hOrdEq, hscj, hGj]
        · change resR.1 (j + 1) = T.S (resR.2.1 j) 0
          rw [hGj1, hscj]
      · exact hCore_rec j (by omega) (by omega)

/-- Exact zero-extension core-state agreement for `Chain.Ordered.algorithm1_initialize`. -/
theorem ordAlgorithm1_initialize_coreAt_eq_zeroExtension
    {T : SparseCoreRestartTool} (hEq : ToolInitOrdEqOnE T)
    (L : LastLevelTool) (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ)
    (G₀ : MGraph) (ℓ₀ g₀ : ℕ → ℝ) (level : ℕ) (hlevel : level < P.d) :
    let st := (Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1
    let G := st.G level
    let len := st.toTreeChain.chainLen ℓ₀ level
    let grad := st.toTreeChain.chainGrad g₀ level
    st.scState level = T.initOrd P.k (lvlM level) N₀ G
      (fun a => if a ∈ G.E then len a else 0)
      (fun a => if a ∈ G.E then grad a else 0)
      (st.levelOrd level) := by
  dsimp only [Chain.Ordered.algorithm1_initialize, ChainState.levelOrd]
  let res := Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ P.d 0
    (fun _ => G₀) (fun _ => T.initOrd P.k (lvlM 0) N₀ G₀ ℓ₀ g₀ (sortedEnds G₀))
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)
  have hcore := (ordRebuildSuffix_prefix_and_coreAt T L P lvlM N₀ ℓ₀ g₀ P.d 0 (by omega)
    (fun _ => G₀) (fun _ => T.initOrd P.k (lvlM 0) N₀ G₀ ℓ₀ g₀ (sortedEnds G₀))
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)).2.2
    level (Nat.zero_le _) (by omega)
  let C1 : TreeChain :=
    { d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
      bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
      lastK := 1, lastLSFs := fun _ => ⟨res.1 level, ⟨res.1 level, ∅⟩, fun _ => 1⟩, lastBran := 0 }
  have hst : res.2.1 level = T.initOrd P.k (lvlM level) N₀ (res.1 level)
      (C1.chainLen ℓ₀ level) (C1.chainGrad g₀ level)
      (Chain.Ordered.chainLevelOrd T res.1 res.2.1 res.2.2.1 level) := hcore.1
  have hlen : C1.chainLen ℓ₀ level =
      (Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1.toTreeChain.chainLen ℓ₀ level :=
    ordTreeChain_chainLen_congr (fun m hm => by
      dsimp only [C1, TreeChain.activeLSF, Chain.Ordered.algorithm1_initialize, ChainState.toTreeChain]
      simp only [show m < P.d by omega, ↓reduceIte]; rfl)
  have hgrad : C1.chainGrad g₀ level =
      (Chain.Ordered.algorithm1_initialize T L P lvlM N₀ G₀ ℓ₀ g₀).1.toTreeChain.chainGrad g₀ level :=
    ordTreeChain_chainGrad_congr (fun _ _ => rfl) (fun m hm => by
      dsimp only [C1, TreeChain.activeLSF, Chain.Ordered.algorithm1_initialize, ChainState.toTreeChain]
      simp only [show m < P.d by omega, ↓reduceIte]; rfl)
  rw [hlen, hgrad] at hst
  exact hst.trans (hEq _ _ _ _ _ _ _ _ _ (fun e he => by rw [ite_eq_left he]; rfl))

/-- Exact zero-extension core-state agreement for `Chain.Ordered.algorithm1_rebuild`. -/
theorem ordAlgorithm1_rebuild_coreAt_eq_zeroExtension
    {T : SparseCoreRestartTool} (hEq : ToolInitOrdEqOnE T)
    (L : LastLevelTool) (P : ChainParams) (chain : ChainState T P)
    (first level : ℕ) (hfirst : first ≤ level) (hlevel : level < P.d)
    (Gnew : MGraph) (enc : ℕ) :
    let next := (Chain.Ordered.algorithm1_rebuild T L P chain first Gnew enc).1
    let G := next.G level
    let len := next.toTreeChain.chainLen chain.ℓ level
    let grad := next.toTreeChain.chainGrad chain.g level
    next.scState level = T.initOrd P.k (chain.lvlM level) chain.N₀ G
      (fun a => if a ∈ G.E then len a else 0)
      (fun a => if a ∈ G.E then grad a else 0)
      (next.levelOrd level) := by
  have hfi : first < P.d := lt_of_le_of_lt hfirst hlevel
  dsimp only [Chain.Ordered.algorithm1_rebuild, ChainState.levelOrd]
  simp only [hfi, ↓reduceDIte]
  let res := Chain.Ordered.rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g (P.d - first) first
    (fun j => if j = first then Gnew else chain.G j)
    chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd
  have hcore := (ordRebuildSuffix_prefix_and_coreAt T L P chain.lvlM chain.N₀ chain.ℓ chain.g
    (P.d - first) first (by omega)
    (fun j => if j = first then Gnew else chain.G j)
    chain.scState chain.bran chain.updCount chain.curEnc chain.curDecUpdates chain.curFwd).2.2
    level hfirst (by omega)
  let C1 : TreeChain :=
    { d := P.d, k := P.k, G := res.1, lsfs := fun m => T.lsfs (res.2.1 m),
      bran := res.2.2.1, S := fun m => T.S (res.2.1 m), emb := fun m => T.emb (res.2.1 m),
      lastK := 1, lastLSFs := fun _ => ⟨res.1 level, ⟨res.1 level, ∅⟩, fun _ => 1⟩, lastBran := 0 }
  have hst : res.2.1 level = T.initOrd P.k (chain.lvlM level) chain.N₀ (res.1 level)
      (C1.chainLen chain.ℓ level) (C1.chainGrad chain.g level)
      (Chain.Ordered.chainLevelOrd T res.1 res.2.1 res.2.2.1 level) := hcore.1
  let stFin := (Chain.Ordered.algorithm1_rebuild T L P chain first Gnew enc).1
  have hstG : ∀ m, stFin.G m = res.1 m := fun m => by
    dsimp only [stFin, Chain.Ordered.algorithm1_rebuild]; simp only [hfi, ↓reduceDIte]; rfl
  have hstSc : ∀ m, stFin.scState m = res.2.1 m := fun m => by
    dsimp only [stFin, Chain.Ordered.algorithm1_rebuild]; simp only [hfi, ↓reduceDIte]; rfl
  have hstBr : ∀ m, stFin.bran m = res.2.2.1 m := fun m => by
    dsimp only [stFin, Chain.Ordered.algorithm1_rebuild]; simp only [hfi, ↓reduceDIte]; rfl
  have hlen : C1.chainLen chain.ℓ level = stFin.toTreeChain.chainLen chain.ℓ level :=
    ordTreeChain_chainLen_congr (fun m hm => by
      dsimp only [C1, TreeChain.activeLSF, ChainState.toTreeChain]
      simp only [show m < P.d by omega, ↓reduceIte, hstSc m, hstBr m])
  have hgrad : C1.chainGrad chain.g level = stFin.toTreeChain.chainGrad chain.g level :=
    ordTreeChain_chainGrad_congr (fun m _ => (hstG m).symm) (fun m hm => by
      dsimp only [C1, TreeChain.activeLSF, ChainState.toTreeChain]
      simp only [show m < P.d by omega, ↓reduceIte, hstSc m, hstBr m])
  rw [hlen, hgrad] at hst
  exact hst.trans (hEq _ _ _ _ _ _ _ _ _ (fun e he => by
    rw [ite_eq_left he]
    exact congrFun (ordTreeChain_chainLen_congr (fun m hm => by
      dsimp only [TreeChain.activeLSF, ChainState.toTreeChain]
      simp only [show m < P.d by omega, ↓reduceIte, hstSc m, hstBr m]; rfl)) e))

/-- Exact `updCount` update under `Chain.Ordered.algorithm1_shift` at `i < P.d`. -/
theorem ordAlgorithm1_shift_updCount_lt {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) {i j : ℕ} (hi : i < P.d) :
    (Chain.Ordered.algorithm1_shift T L P chain i).1.updCount j =
      if i + 1 ≤ j ∧ j < P.d then 0 else chain.updCount j := by
  unfold Chain.Ordered.algorithm1_shift
  rw [dite_eq_left hi]
  dsimp only
  have h := ordRebuildSuffix_prefix_and_coreAt T L P chain.lvlM chain.N₀ chain.ℓ chain.g
    (P.d - (i + 1)) (i + 1) (by omega)
    (fun j => if j = i + 1 then T.S (T.restart (chain.scState i) ((chain.bran i + 1) % P.k))
        ((chain.bran i + 1) % P.k) else chain.G j)
    (fun j => if j = i then T.restart (chain.scState i) ((chain.bran i + 1) % P.k)
      else chain.scState j)
    (fun j => if j = i then (chain.bran i + 1) % P.k else chain.bran j)
    chain.updCount
    (fun j => if j = i + 1 then 0 else chain.curEnc j)
    (fun j => if j = i then 0 else chain.curDecUpdates j)
    chain.curFwd
  by_cases hj : i + 1 ≤ j ∧ j < P.d
  · rw [ite_eq_left hj]
    exact (h.2.2 j hj.1 (by omega)).2.2.2
  · rw [ite_eq_right hj]
    by_cases hlt : j < i + 1
    · exact (h.2.1 j hlt).2.2
    · -- `P.d ≤ j`: `rebuildSuffix` only touches `idx ≤ k < idx + rem`
      have hge : P.d ≤ j := by omega
      clear h hlt hj
      suffices hpres : ∀ (rem first : ℕ) (Gf : ℕ → MGraph) (sc : ℕ → T.State)
          (br upd ce cd cf : ℕ → ℕ), first + rem ≤ j →
          (Chain.Ordered.rebuildSuffix T L P chain.lvlM chain.N₀ chain.ℓ chain.g
            rem first Gf sc br upd ce cd cf).2.2.2.1 j = upd j by
        exact hpres (P.d - (i + 1)) (i + 1) _ _ _ _ _ _ _ (by omega)
      intro rem
      induction rem with
      | zero => intros; rfl
      | succ rem ih =>
        intro first Gf sc br upd ce cd cf hle
        dsimp only [Chain.Ordered.rebuildSuffix]
        rw [ih (first + 1) _ _ _ _ _ _ _ (by omega)]
        simp [show j ≠ first by omega]

/-- Exact `updCount` preservation under `Chain.Ordered.algorithm1_shift` at terminal `i = P.d`. -/
theorem ordAlgorithm1_shift_updCount_eq {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) {j : ℕ} :
    (Chain.Ordered.algorithm1_shift T L P chain P.d).1.updCount j = chain.updCount j := by
  unfold Chain.Ordered.algorithm1_shift
  rw [dite_eq_right (Nat.lt_irrefl _)]

/-- Exact `rebuildCount` preservation under `Chain.Ordered.algorithm1_shift`. -/
theorem ordAlgorithm1_shift_rebuildCount {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) (i j : ℕ) :
    (Chain.Ordered.algorithm1_shift T L P chain i).1.rebuildCount j = chain.rebuildCount j := by
  unfold Chain.Ordered.algorithm1_shift
  split_ifs <;> rfl

/-- Exact `shiftCount` update under `Chain.Ordered.algorithm1_shift` at `i ≤ P.d`. -/
theorem ordAlgorithm1_shift_shiftCount {T : SparseCoreRestartTool} {L : LastLevelTool}
    {P : ChainParams} (chain : ChainState T P) {i j : ℕ} (hi : i ≤ P.d) :
    (Chain.Ordered.algorithm1_shift T L P chain i).1.shiftCount j =
      if j = i then chain.shiftCount i + 1 else chain.shiftCount j := by
  unfold Chain.Ordered.algorithm1_shift
  by_cases hlt : i < P.d
  · rw [dite_eq_left hlt]
  · rw [dite_eq_right hlt]
    have heq : i = P.d := by omega
    subst heq; rfl

end OrderedSuffixAgreement

section TelescopingCost

/-- Telescoping sum for any monotone sequence of cumulative tool costs `c : ℕ → ℕ`. -/
theorem ordCoreCost_telescope (c : ℕ → ℕ) :
    ∀ n : ℕ, (∀ t < n, c t ≤ c (t + 1)) →
      c 0 + ∑ t ∈ Finset.range n, (c (t + 1) - c t) = c n := by
  intro n
  induction n with
  | zero => intro _; simp
  | succ n ih =>
    intro hmono
    rw [Finset.sum_range_succ, ← add_assoc, ih (fun t ht => hmono t (Nat.lt_succ_of_lt ht))]
    have hlast := hmono n (Nat.lt_succ_self n)
    omega

/-- `P.mul`-scaled telescoping budget across an initial state `c 0` and `n` update/restart steps
with per-step word overhead `overhead t`. -/
theorem ordCoreCost_telescope_scaled (mul : ℕ) (c overhead : ℕ → ℕ) (initExtra n : ℕ)
    (hmono : ∀ t < n, c t ≤ c (t + 1)) :
    mul * (c 0 + initExtra) +
        ∑ t ∈ Finset.range n, mul * (c (t + 1) - c t + overhead t) =
      mul * (c n + initExtra + ∑ t ∈ Finset.range n, overhead t) := by
  have hsum :
      ∑ t ∈ Finset.range n, mul * (c (t + 1) - c t + overhead t) =
        mul * (∑ t ∈ Finset.range n, (c (t + 1) - c t) + ∑ t ∈ Finset.range n, overhead t) := by
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
  rw [hsum, ← mul_add]
  congr 1
  have htel := ordCoreCost_telescope c n hmono
  omega

end TelescopingCost

end MinCostFlow.MinRatio
