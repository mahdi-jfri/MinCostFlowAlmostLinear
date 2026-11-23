module

public import MinCostFlow.MinRatio.WireInitPrefix

/-!
# Arithmetic helper lemmas for `WireInitConcreteCore`

Bundles the layout inequalities (`CCStage12Arith`, `CCStage3Arith`, `CCStage4Arith`) and
space/cost composition lemmas for `initConcreteBody_runs` (`WireInitConcreteCore`), using the
allocated root edge capacity `eCap ≤ capLimit` and the `(4 * d + 4)` metadata/select-pointer block
before `handle = solverHandleAddr table d`.
-/

public section

namespace MinCostFlow.MinRatio

open Chain SparseCore.Program DynSpanner.Program

structure CCStage12Arith (w root L m n eCap d paramSpace capExp capLimit lastSpace
    treeInitSpace linkSpace : ℕ) (coreInitSpace lvlM nextM : ℕ → ℕ) (N₀ : ℕ) : Prop where
  room1 : root + 16 + (L + 1) + 6 + paramSpace < 2 ^ w
  root16_le_pBase : root + 16 ≤ root + 16 + (L + 1) + 6
  room2 : ∀ rootGraph, rootGraph ≤ root + 16 + (L + 1) + 6 + paramSpace →
    rootGraph + dynGraphSize n eCap + (1 + 4 * n + 2 * eCap) + eCap * L + (4 * d + 4) + 18 < 2 ^ w
  eCap_lt_w : eCap < 2 ^ w

theorem mkCCStage12Arith {w root L m n eCap d paramSpace capExp capLimit lastSpace
    treeInitSpace linkSpace : ℕ} {coreInitSpace lvlM nextM : ℕ → ℕ} {N₀ : ℕ}
    (heCapLe : eCap ≤ capLimit)
    (hroom : root + initConcreteSpace m n L d paramSpace capExp capLimit lastSpace
      treeInitSpace linkSpace coreInitSpace lvlM nextM N₀ < 2 ^ w) :
    CCStage12Arith w root L m n eCap d paramSpace capExp capLimit lastSpace
      treeInitSpace linkSpace coreInitSpace lvlM nextM N₀ := by
  have hdgLe : dynGraphSize n eCap ≤ dynGraphSize n capLimit := by unfold dynGraphSize; omega
  have hmulLe : eCap * L ≤ capLimit * L := Nat.mul_le_mul_right L heCapLe
  have hdgCap : dynGraphSize n capLimit = 4 + 7 * n + 9 * capLimit := rfl
  dsimp only [initConcreteSpace] at hroom
  exact ⟨by omega, by omega, fun _ _ => by omega, by omega⟩

structure CCStage3Arith (w root rootGraph L m n eCap d paramSpace capExp capLimit lastSpace
    treeInitSpace linkSpace ordBase len0Buf table : ℕ)
    (coreInitSpace lvlM nextM : ℕ → ℕ) (N₀ : ℕ) : Prop where
  one_lt_w : 1 < 2 ^ w
  zero_lt_w : 0 < 2 ^ w
  d1_lt_w : d + 1 < 2 ^ w
  d_lt_w : d < 2 ^ w
  L_lt_w : L < 2 ^ w
  nine_lt_w : 9 < 2 ^ w
  root_le_pBase : root ≤ root + 16 + (L + 1) + 6
  root_le_rootG : root ≤ rootGraph
  rootG_end_le_len0 : rootGraph + dynGraphSize n eCap ≤ len0Buf
  rootG_end_le_meta : rootGraph + dynGraphSize n eCap ≤ solverLevelMetaAddr table d
  len0_end_le_meta : len0Buf + eCap * L ≤ solverLevelMetaAddr table d
  root_le_lvl : root ≤ solverHandleAddr table d + 18
  ordWords_le : 1 + 2 * n + 2 * m ≤ 2 * N₀ + 2 * lvlM 0 + 1
  ordEnd_le_lvl : ordBase + (1 + 2 * n + 2 * m) ≤ solverHandleAddr table d + 18
  handle18_le_lvlStart :
    solverHandleAddr table d + 18 ≤ solverHandleAddr table d + 18 + (d + 1) + (d + 1)
  br_lt_w : solverHandleAddr table d + 18 + (d + 1) < 2 ^ w
  lvlStart_lt_w : solverHandleAddr table d + 18 + (d + 1) + (d + 1) < 2 ^ w
  room3 : solverHandleAddr table d + 18 + (d + 1) + (d + 1) +
    ordInitLevelsSpace L capExp capLimit coreInitSpace lvlM nextM N₀ lastSpace d < 2 ^ w

theorem mkCCStage3Arith {w root rootGraph L m n eCap d paramSpace capExp capLimit lastSpace
    treeInitSpace linkSpace ordBase len0Buf table : ℕ}
    {coreInitSpace lvlM nextM : ℕ → ℕ} {N₀ : ℕ}
    (hrgLo : root + 16 + (L + 1) + 6 + 7 + d ≤ rootGraph)
    (hrgHi : rootGraph ≤ root + 16 + (L + 1) + 6 + paramSpace)
    (hordEq : ordBase = rootGraph + dynGraphSize n eCap)
    (hlen0Eq : len0Buf = ordBase + 1 + 4 * n + 2 * eCap)
    (htableEq : table = len0Buf + eCap * L)
    (hmLeECap : m ≤ eCap) (heCapLe : eCap ≤ capLimit)
    (hGnLeN : n ≤ N₀) (hGmLeM0 : m ≤ lvlM 0) (hw17 : 17 < 2 ^ w)
    (hroom : root + initConcreteSpace m n L d paramSpace capExp capLimit lastSpace
      treeInitSpace linkSpace coreInitSpace lvlM nextM N₀ < 2 ^ w) :
    CCStage3Arith w root rootGraph L m n eCap d paramSpace capExp capLimit lastSpace
      treeInitSpace linkSpace ordBase len0Buf table coreInitSpace lvlM nextM N₀ := by
  have hdgLe : dynGraphSize n eCap ≤ dynGraphSize n capLimit := by unfold dynGraphSize; omega
  have hmulLe : eCap * L ≤ capLimit * L := Nat.mul_le_mul_right L heCapLe
  have hhDef : solverHandleAddr table d = table + (4 * d + 4) := by
    unfold solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr
      solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  dsimp only [initConcreteSpace] at hroom
  refine ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega,
    by omega, by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega,
    by unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega,
    by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

structure CCStage4Arith (w root rootGraph L m n eCap d paramSpace capExp capLimit lastSpace
    treeInitSpace linkSpace ordBase len0Buf table levelsEnd : ℕ)
    (coreInitSpace lvlM nextM : ℕ → ℕ) (N₀ : ℕ) : Prop where
  handle18_le_levEnd : solverHandleAddr table d + 18 ≤ levelsEnd
  rootG_end_le_len0 : rootGraph + dynGraphSize n eCap ≤ len0Buf
  rootG_end_le_table : rootGraph + dynGraphSize n eCap ≤ table
  rootG2_lt_levEnd : rootGraph + 2 < levelsEnd
  treeHeap_plus_init_lt_w :
    levelsEnd + (4 * (d + 1) + 1) + 1 + m + m + m + treeInitSpace < 2 ^ w
  levEnd_le_treeHeap : levelsEnd ≤ levelsEnd + (4 * (d + 1) + 1) + 1 + m + m + m
  levEnd_lt_w : levelsEnd < 2 ^ w
  handle18_lt_lvlStart :
    solverHandleAddr table d + 18 ≤ solverHandleAddr table d + 18 + (d + 1) + (d + 1)
  handle18_le_br : solverHandleAddr table d + 18 ≤ solverHandleAddr table d + 18 + (d + 1)

theorem mkCCStage4Arith {w root rootGraph L m n eCap d paramSpace capExp capLimit lastSpace
    treeInitSpace linkSpace ordBase len0Buf table levelsEnd : ℕ}
    {coreInitSpace lvlM nextM : ℕ → ℕ} {N₀ : ℕ}
    (hrgHi : rootGraph ≤ root + 16 + (L + 1) + 6 + paramSpace)
    (hordEq : ordBase = rootGraph + dynGraphSize n eCap)
    (hlen0Eq : len0Buf = ordBase + 1 + 4 * n + 2 * eCap)
    (htableEq : table = len0Buf + eCap * L)
    (heCapLe : eCap ≤ capLimit)
    (hlevLo : solverHandleAddr table d + 18 + (d + 1) + (d + 1) ≤ levelsEnd)
    (hlevHi : levelsEnd ≤ solverHandleAddr table d + 18 + (d + 1) + (d + 1) +
      ordInitLevelsSpace L capExp capLimit coreInitSpace lvlM nextM N₀ lastSpace d)
    (hroom : root + initConcreteSpace m n L d paramSpace capExp capLimit lastSpace
      treeInitSpace linkSpace coreInitSpace lvlM nextM N₀ < 2 ^ w) :
    CCStage4Arith w root rootGraph L m n eCap d paramSpace capExp capLimit lastSpace
      treeInitSpace linkSpace ordBase len0Buf table levelsEnd coreInitSpace lvlM nextM N₀ := by
  have hdg : dynGraphSize n eCap = 4 + 7 * n + 9 * eCap := rfl
  have hdgLe : dynGraphSize n eCap ≤ dynGraphSize n capLimit := by unfold dynGraphSize; omega
  have hmulLe : eCap * L ≤ capLimit * L := Nat.mul_le_mul_right L heCapLe
  have hhDef : solverHandleAddr table d = table + (4 * d + 4) := by
    unfold solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr
      solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  dsimp only [initConcreteSpace] at hroom
  exact ⟨by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩

theorem reg_ne_stage3 {r : ℕ} (hr : r = 67 ∨ r = 68 ∨ 70 ≤ r) :
    r ≠ 21 ∧ r ≠ 20 ∧ r ≠ 8 ∧ r ≠ 7 ∧ r ≠ 6 ∧ r ≠ 1 ∧ r ≠ 4 ∧ r ≠ 52 ∧ r ≠ 51 ∧ r ≠ 57 := by
  rcases hr with rfl | rfl | h <;> omega

theorem initConcrete_roomPost_and_space
    {w root rootGraph L m n eCap d paramSpace capExp capLimit lastSpace treeInitSpace linkSpace
      ordBase len0Buf table levelsEnd treeEnd : ℕ}
    {coreInitSpace lvlM nextM : ℕ → ℕ} {N₀ : ℕ}
    (hrgHi : rootGraph ≤ root + 16 + (L + 1) + 6 + paramSpace)
    (hordEq : ordBase = rootGraph + dynGraphSize n eCap)
    (hlen0Eq : len0Buf = ordBase + 1 + 4 * n + 2 * eCap)
    (htableEq : table = len0Buf + eCap * L)
    (heCapLe : eCap ≤ capLimit)
    (hlevHi : levelsEnd ≤ solverHandleAddr table d + 18 + (d + 1) + (d + 1) +
      ordInitLevelsSpace L capExp capLimit coreInitSpace lvlM nextM N₀ lastSpace d)
    (htreeHi : treeEnd ≤ levelsEnd + (4 * (d + 1) + 1) + 1 + m + m + m + treeInitSpace)
    (hroom : root + initConcreteSpace m n L d paramSpace capExp capLimit lastSpace
      treeInitSpace linkSpace coreInitSpace lvlM nextM N₀ < 2 ^ w) :
    treeEnd + initPostTailSpace m n L d linkSpace ≤
      root + initConcreteSpace m n L d paramSpace capExp capLimit lastSpace
        treeInitSpace linkSpace coreInitSpace lvlM nextM N₀ ∧
    treeEnd + initPostTailSpace m n L d linkSpace < 2 ^ w := by
  have hdgLe : dynGraphSize n eCap ≤ dynGraphSize n capLimit := by unfold dynGraphSize; omega
  have hmulLe : eCap * L ≤ capLimit * L := Nat.mul_le_mul_right L heCapLe
  have hhDef : solverHandleAddr table d = table + (4 * d + 4) := by
    unfold solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr
      solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  dsimp only [initConcreteSpace] at hroom ⊢
  omega

theorem initConcrete_root_le_fin
    {root levelsEnd treeEnd finalHeap d m n L : ℕ}
    (h1 : root ≤ levelsEnd)
    (h2 : levelsEnd + (4 * (d + 1) + 1) + 1 + m + m + m ≤ treeEnd)
    (h3 : treeEnd + m + 2 * n + 2 * n + m + m + m + 3 * L + m * initEdgeRecordSpace L ≤ finalHeap) :
    root ≤ finalHeap := by
  omega

theorem initConcrete_totalCost_le
    {c1 c2 cLevels cTail cPost m n eCap L d paramCost capExp capLimit lastMult treeConst
      treePhi0 treePhiFin corePhi3 corePhiFin totalRuntime mul : ℕ}
    {P_sc : SparseCoreOrdParams} {lvlM nextM : ℕ → ℕ} {N₀ : ℕ}
    (heCapLe : eCap ≤ capLimit)
    (hc1 : c1 ≤ paramCost + 22 * Nat.clog 2 (N₀ + 2) + 150)
    (hc2 : c2 ≤ (130 * n + 490 * m) + (150 * eCap + 60 * n) + 30 * (m * L) + 30 * d + 610)
    (hcLevels : cLevels + corePhi3 ≤
      ordInitLevelsFixed L capExp capLimit P_sc lvlM nextM N₀ lastMult d + 26 * d +
        mul * totalRuntime)
    (hcTail : cTail + treePhi0 ≤ treeConst * (L + 1) ^ 2 * (n + 1) + 20 * m + 92)
    (hcPost : cPost + treePhiFin + corePhiFin ≤
      initPostTailCost m n L d treeConst P_sc.readout + treePhi0 + corePhi3) :
    (c1 + (c2 + ((2 + (2 + (6 + (6 + (2 + (2 + (2 + (2 + (2 + (2 + cLevels + 1) + 1) + 1) + 1) +
        1) + 1) + 1) + 1) + 1) + 1) +
      (2 + (cTail + (cPost + 2 + 1) + 1) + 1) + 1) + 1) + 1) + treePhiFin + corePhiFin ≤
      initConcreteFixed m n L d paramCost capExp capLimit lastMult treeConst P_sc lvlM nextM N₀ +
        mul * totalRuntime := by
  dsimp only [initConcreteFixed]
  omega

theorem initConcrete_packMeta5
    {T : SparseCoreRestartTool} {C : ChainParams} {G : MGraph}
    {L P m eCap root rootGraph len0Buf table levelsEnd N₀ : ℕ} {lvlM : ℕ → ℕ}
    {len₀ : ℕ → ℝ} {chain : Chain.ChainState T C}
    {m2 m3 m5 : ℕ → ℕ}
    (hG0Eq : chain.G 0 = G) (hGE : G.E = Finset.range m) (hmLeECap : m ≤ eCap)
    (hN0Eq : chain.N₀ = N₀) (hLvlMEq : ∀ j < C.d, chain.lvlM j = lvlM j)
    (hroot16 : root + 16 ≤ rootGraph)
    (hrootGLe : rootGraph + dynGraphSize G.n eCap ≤ len0Buf)
    (htableEq : table = len0Buf + eCap * L)
    (hmem5_preH : ∀ a, root + 16 ≤ a → a < solverHandleAddr table C.d → m5 a = m3 a)
    (hmem3_preMeta : ∀ a, a ≤ solverLevelMetaAddr table C.d → m3 a = m2 a)
    (hmem3_sel : m3 (solverSelectHeapAddr table C.d) = m2 (solverSelectHeapAddr table C.d) ∧
      m3 (solverSelectBlocksAddr table C.d) = m2 (solverSelectBlocksAddr table C.d))
    (hmem5_meta : ∀ a,
      (∃ j, 1 ≤ j ∧ j < C.d ∧
        ((m3 (solverLevelMetaAddr table C.d + j) ≤ a ∧
            a < m3 (solverLevelMetaAddr table C.d + j) + eCap * L) ∨
         (m3 (solverLevelMetaAddr table C.d + C.d + j) ≤ a ∧
            a < m3 (solverLevelMetaAddr table C.d + C.d + j) + dynGraphSize G.n eCap))) →
      m5 a = m3 a)
    (hn0_2 : m2 (solverN0Addr table C.d) = N₀)
    (hlvlCopy2 : ∀ j < C.d, m2 (solverLvlMAddr table C.d + j) = lvlM j)
    (hmeta0_2 : m2 (solverLevelMetaAddr table C.d) = len0Buf)
    (hmetaG0_2 : m2 (solverLevelMetaAddr table C.d + C.d) = rootGraph)
    (hsel0_2 : m2 (solverSelectHeapAddr table C.d) = 0 ∧
      m2 (solverSelectBlocksAddr table C.d) = 0)
    (hmem3_metaG0 : m3 (solverLevelMetaAddr table C.d + C.d) =
      m2 (solverLevelMetaAddr table C.d + C.d))
    (hLen2 : EdgeValuesAt m2 len0Buf 4 L P G.E len₀)
    (hhandles : ∀ j < C.d,
      solverHandleAddr table C.d + 18 + (C.d + 1) + (C.d + 1) ≤
        m5 (solverHandleAddr table C.d + 18 + j) ∧
      m5 (solverHandleAddr table C.d + 18 + j) ≤ levelsEnd)
    (hmetaLevels3 : ∀ j, 1 ≤ j → j < C.d →
      DynGraphAt m3 (m3 (solverLevelMetaAddr table C.d + C.d + j)) G.n eCap (chain.G j) ∧
      solverHandleAddr table C.d + 18 + (C.d + 1) + (C.d + 1) ≤
        m3 (solverLevelMetaAddr table C.d + C.d + j) ∧
      m3 (solverLevelMetaAddr table C.d + C.d + j) + dynGraphSize G.n eCap ≤ levelsEnd ∧
      EdgeValuesAt m3 (m3 (solverLevelMetaAddr table C.d + j)) 4 L P (chain.G j).E
        (chain.toTreeChain.chainLen len₀ j) ∧
      solverHandleAddr table C.d + 18 + (C.d + 1) + (C.d + 1) ≤
        m3 (solverLevelMetaAddr table C.d + j) ∧
      m3 (solverLevelMetaAddr table C.d + j) + eCap * L ≤ levelsEnd)
    (hmetaOrd3 :
      (∀ j, 1 ≤ j → j < C.d →
        m3 (solverLevelMetaAddr table C.d + C.d + j) + dynGraphSize G.n eCap ≤
          m3 (solverLevelMetaAddr table C.d + j)) ∧
      (∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ < C.d →
        m3 (solverLevelMetaAddr table C.d + j₁) + eCap * L ≤
          m3 (solverLevelMetaAddr table C.d + C.d + j₂))) :
    let n0Cell := solverN0Addr table C.d
    let lvlMTable := solverLvlMAddr table C.d
    let levelMeta := solverLevelMetaAddr table C.d
    let handle := solverHandleAddr table C.d
    let levelTable := handle + 18
    let branchTable := levelTable + (C.d + 1)
    ((fun a => ∃ j, 1 ≤ j ∧ j < C.d ∧
        ((m5 (levelMeta + j) ≤ a ∧ a < m5 (levelMeta + j) + eCap * L) ∨
         (m5 (levelMeta + C.d + j) ≤ a ∧ a < m5 (levelMeta + C.d + j) + dynGraphSize G.n eCap))) =
      (fun a => ∃ j, 1 ≤ j ∧ j < C.d ∧
        ((m3 (levelMeta + j) ≤ a ∧ a < m3 (levelMeta + j) + eCap * L) ∨
         (m3 (levelMeta + C.d + j) ≤ a ∧ a < m3 (levelMeta + C.d + j) + dynGraphSize G.n eCap)))) ∧
    (m5 (solverSelectHeapAddr table C.d) = 0 ∧ m5 (solverSelectBlocksAddr table C.d) = 0) ∧
    (m5 n0Cell = chain.N₀ ∧
      (∀ j < C.d, m5 (lvlMTable + j) = chain.lvlM j) ∧
      (∀ j < C.d, branchTable + (C.d + 1) ≤ m5 (levelTable + j) ∧ m5 (levelTable + j) ≤ levelsEnd) ∧
      m5 (levelMeta + 0) = len0Buf ∧
      m5 (levelMeta + C.d + 0) = rootGraph ∧
      EdgeValuesAt m5 len0Buf 4 L P (chain.G 0).E (chain.toTreeChain.chainLen len₀ 0) ∧
      (∀ j, 1 ≤ j → j < C.d →
        DynGraphAt m5 (m5 (levelMeta + C.d + j)) G.n eCap (chain.G j) ∧
        EdgeValuesAt m5 (m5 (levelMeta + j)) 4 L P (chain.G j).E
          (chain.toTreeChain.chainLen len₀ j) ∧
        branchTable + (C.d + 1) ≤ m5 (levelMeta + j) ∧
        m5 (levelMeta + j) + eCap * L ≤ levelsEnd ∧
        branchTable + (C.d + 1) ≤ m5 (levelMeta + C.d + j) ∧
        m5 (levelMeta + C.d + j) + dynGraphSize G.n eCap ≤ levelsEnd)) ∧
    ((∀ j, 1 ≤ j → j < C.d →
        m5 (levelMeta + C.d + j) + dynGraphSize G.n eCap ≤ m5 (levelMeta + j)) ∧
      (∀ j₁ j₂, 1 ≤ j₁ → j₁ < j₂ → j₂ < C.d →
        m5 (levelMeta + j₁) + eCap * L ≤ m5 (levelMeta + C.d + j₂))) := by
  intro n0Cell lvlMTable levelMeta handle levelTable branchTable
  have hdPos : 0 < C.d := C.hd
  have hn0D : n0Cell = table + (C.d + 1) := rfl
  have hlmD : lvlMTable = n0Cell + 1 := rfl
  have hmetD : levelMeta = lvlMTable + C.d := rfl
  have hshD : solverSelectHeapAddr table C.d = levelMeta + 2 * C.d := rfl
  have hsbD : solverSelectBlocksAddr table C.d = levelMeta + 2 * C.d + 1 := rfl
  have hhD : handle = table + (4 * C.d + 4) := by
    unfold handle solverHandleAddr solverSelectBlocksAddr solverSelectHeapAddr
      solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega
  have hmLLe : m * L ≤ eCap * L := Nat.mul_le_mul_right L hmLeECap
  have hpreMeta (a : ℕ) (h1 : root + 16 ≤ a) (h2 : a ≤ levelMeta) : m5 a = m2 a :=
    (hmem5_preH a h1 (by omega)).trans (hmem3_preMeta a (by omega))
  have hLptr (j : ℕ) (hj : j < C.d) : m5 (levelMeta + j) = m3 (levelMeta + j) :=
    hmem5_preH _ (by omega) (by omega)
  have hGptr (j : ℕ) (hj : j < C.d) : m5 (levelMeta + C.d + j) = m3 (levelMeta + C.d + j) :=
    hmem5_preH _ (by omega) (by omega)
  have hMetaEq :
      (fun a => ∃ j, 1 ≤ j ∧ j < C.d ∧
        ((m5 (levelMeta + j) ≤ a ∧ a < m5 (levelMeta + j) + eCap * L) ∨
         (m5 (levelMeta + C.d + j) ≤ a ∧ a < m5 (levelMeta + C.d + j) + dynGraphSize G.n eCap))) =
      (fun a => ∃ j, 1 ≤ j ∧ j < C.d ∧
        ((m3 (levelMeta + j) ≤ a ∧ a < m3 (levelMeta + j) + eCap * L) ∨
         (m3 (levelMeta + C.d + j) ≤ a ∧ a < m3 (levelMeta + C.d + j) + dynGraphSize G.n eCap))) := by
    funext a; apply propext
    constructor
    · rintro ⟨j, hj1, hjLt, h⟩; rw [hLptr j hjLt, hGptr j hjLt] at h; exact ⟨j, hj1, hjLt, h⟩
    · rintro ⟨j, hj1, hjLt, h⟩; refine ⟨j, hj1, hjLt, ?_⟩; rwa [hLptr j hjLt, hGptr j hjLt]
  have hLen0 : EdgeValuesAt m5 len0Buf 4 L P (chain.G 0).E (chain.toTreeChain.chainLen len₀ 0) := by
    have hcl0 : chain.toTreeChain.chainLen len₀ 0 = len₀ := rfl
    rw [hG0Eq, hcl0]
    exact hLen2.congr (fun e he r hr => by
      have hem : e < m := Finset.mem_range.mp (hGE ▸ he)
      have hmul : e * L + L ≤ m * L := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (Nat.succ_le_of_lt hem)
      exact hpreMeta (len0Buf + e * L + r) (by omega) (by omega))
  refine ⟨hMetaEq,
    ⟨(hmem5_preH _ (by omega) (by omega)).trans (hmem3_sel.1.trans hsel0_2.1),
     (hmem5_preH _ (by omega) (by omega)).trans (hmem3_sel.2.trans hsel0_2.2)⟩,
    ⟨(hpreMeta n0Cell (by omega) (by omega)).trans (hn0_2.trans hN0Eq.symm),
     fun j hj => (hpreMeta (lvlMTable + j) (by omega) (by omega)).trans
       ((hlvlCopy2 j hj).trans (hLvlMEq j hj).symm),
     hhandles,
     (hpreMeta levelMeta (by omega) le_rfl).trans hmeta0_2,
     (hmem5_preH (levelMeta + C.d) (by omega) (by omega)).trans (hmem3_metaG0.trans hmetaG0_2),
     hLen0, fun j hj1 hjLt => ?_⟩,
    ⟨fun j hj1 hjLt => by rw [hGptr j hjLt, hLptr j hjLt]; exact hmetaOrd3.1 j hj1 hjLt,
     fun j₁ j₂ hj1 hlt hj2Lt => by rw [hLptr j₁ (lt_trans hlt hj2Lt), hGptr j₂ hj2Lt]; exact hmetaOrd3.2 j₁ j₂ hj1 hlt hj2Lt⟩⟩
  obtain ⟨hDG3J, hGLo3, hGHi3, hLen3J, hLLo3, hLHi3⟩ := hmetaLevels3 j hj1 hjLt
  rw [hLptr j hjLt, hGptr j hjLt]
  refine ⟨dynGraphAt_of_agree hDG3J (fun a hlo hhi => hmem5_meta a ⟨j, hj1, hjLt, Or.inr ⟨hlo, hhi⟩⟩),
    hLen3J.congr (fun e he r hr => by
      have heLt : e < eCap := hDG3J.2.2.1 e he
      have hmul : e * L + L ≤ eCap * L := by
        rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right L (Nat.succ_le_of_lt heLt)
      have ha1 : m3 (levelMeta + j) ≤ m3 (levelMeta + j) + e * L + r := by omega
      have ha2 : m3 (levelMeta + j) + e * L + r < m3 (levelMeta + j) + eCap * L := by omega
      exact hmem5_meta (m3 (levelMeta + j) + e * L + r) ⟨j, hj1, hjLt, Or.inl ⟨ha1, ha2⟩⟩),
    hLLo3, hLHi3, hGLo3, hGHi3⟩

end MinCostFlow.MinRatio
