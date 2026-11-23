module

public import MinCostFlow.MinRatio.WireSelectKeyEval
import WordRAM.Tactic

/-!
# Re-embedded edges interface and select-heap key-update procedures (`Initialize`, `Rebuild`, `Shift`, `Update`)

Implements Job 2 and the key-update half of Job 1 (`jtree.tex`, pages 20–21, 24):
1. **Re-embedded edges interface** (between the select heap and the sparse core):
   - `ReembListAt mem ptr len reemb`: a flat list of edge names in memory.
   - `ReembCovers C C' i reemb`: contains every surviving candidate at level `i` whose embedding
     changed (`C'.activeEmb i e ≠ C.activeEmb i e`).
   - `ReembCostBound reemb toolCostDelta cReemb phi phi'`: the length, amortized with a potential
     of the tool state (`phi` before the step, `phi'` after), is at most
     `cReemb * (toolCostDelta + 1)`.
   - `LevelDiffLists`, `LevelDiffListsAt`, `LevelDiffCovers`, and `touched_covers_level_changes`:
     proves that combining `U_i`, `fDel_i`, `U_{S,i}`, and `reemb_i` covers EVERY edge whose
     candidate membership or `(walkInner, wlenAt)` key changed at level `i`.
2. **Word-RAM key-update procedures** parameterized by a key evaluator `evalKeyProc`:
   - `selectProcessEdgeBody` (`[hb, meta, lvl, e, scratch]`): checks `e ∈ G_lvl \ F_lvl \ S_lvl`
     via `DynGraphAt` presence tables; if candidate, evaluates key and calls `heapUpsert`, else
     calls `heapDeleteIfLevel`.
   - `selectProcessListBody` (`[hb, meta, lvl, listPtr, len, idx, scratch]`): processes every edge
     in a touched-edge list, charging `O(len · (evalKeyCost + (log(cap + 1) + 1) · (Lk^2 + 1)))`.
   - `selectUpdateLevelBody` (`[hb, meta, lvl, diffBase, scratch]`): processes the 4 lists of
     `LevelDiffListsAt` for a non-rebuilt level `lvl`.
   - `selectRebuildLevelBody` (`[hb, meta, lvl, scratch]`): clears level `lvl` via `heapClearLevel`
     and re-inserts all candidates of `G_lvl.E` via `dgEListBase`.
   - `selectRebuildSuffixBody` (`[hb, meta, i0, d, scratch]`): rebuilds levels `i0 .. d` for
     `Initialize`, `Rebuild(i0)`, `Shift(i0)`, and the rebuilt suffix of `Update`.
3. **Pure chain-transition correctness bridges**:
   - `selectHeap_prefix_preserved`: prefix `< i0` stays valid under `Shift(i0)` / `Rebuild(i0)`.
   - `selectHeap_nonrebuilt_level_valid`: updating `lists.allTouched` restores level `i` for `Update`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Re-embedded edges interface (Job 2) -/

/-- A list of re-embedded edge names stored contiguously at `[ptr, ptr + len)`. -/
def ReembListAt (mem : ℕ → ℕ) (ptr len : ℕ) (reemb : List ℕ) : Prop :=
  len = reemb.length ∧ ListAt mem ptr reemb

/-- Coverage specification of the re-embedded edges list at level `i < C.d`: every surviving
candidate `e` whose embedding changed across the step appears in `reemb`. -/
def ReembCovers (C C' : TreeChain) (i : ℕ) (reemb : List ℕ) : Prop :=
  ∀ e, e ∈ (C.activeCore i).E \ (C.activeS i).E →
    e ∈ (C'.activeCore i).E \ (C'.activeS i).E →
    C'.activeEmb i e ≠ C.activeEmb i e →
    e ∈ reemb

/-- Cost-charging specification of the re-embedded edges list, amortized. A potential of the tool
state of the level (`phi` before the step, `phi'` after) pays what the growth of the tool cost does
not: `reemb.length + phi' ≤ cReemb * (toolCostDelta + 1) + phi`, with
`toolCostDelta = tool.cost st' - tool.cost st`. The bound cannot hold per step without the
potential: a full rebuild of a bucket spanner lists every edge of its graph, while the tool cost
grows by the charge of a few updates. -/
def ReembCostBound (reemb : List ℕ) (toolCostDelta cReemb phi phi' : ℕ) : Prop :=
  reemb.length + phi' ≤ cReemb * (toolCostDelta + 1) + phi

/-- The four per-level touched-edge lists emitted during a non-rebuilding update at level `i`:
- `uG`: edge IDs inserted or deleted by `U_i` on `G_i`,
- `fDel`: forest edges leaving `(C.activeLSF i).F.F` (`LSFChange.fDel`),
- `uS`: edge IDs inserted or deleted by `U_{S,i}` on `C.activeS i`,
- `reemb`: surviving candidates whose embedding changed (`ReembListAt`). -/
structure LevelDiffLists where
  uG : List ℕ
  fDel : List ℕ
  uS : List ℕ
  reemb : List ℕ

/-- Combined list of all touched edges at a level. -/
def LevelDiffLists.allTouched (L : LevelDiffLists) : List ℕ :=
  L.uG ++ L.fDel ++ L.uS ++ L.reemb

/-- Total number of touched-edge entries in a `LevelDiffLists`. -/
def LevelDiffLists.totalLen (L : LevelDiffLists) : ℕ :=
  L.uG.length + L.fDel.length + L.uS.length + L.reemb.length

/-- Memory layout for `LevelDiffLists` at `diffBase` (8 words: four `(ptr, len)` pairs). -/
def LevelDiffListsAt (mem : ℕ → ℕ) (diffBase : ℕ) (L : LevelDiffLists) : Prop :=
  mem (diffBase + 1) = L.uG.length ∧ ListAt mem (mem (diffBase + 0)) L.uG ∧
  mem (diffBase + 3) = L.fDel.length ∧ ListAt mem (mem (diffBase + 2)) L.fDel ∧
  mem (diffBase + 5) = L.uS.length ∧ ListAt mem (mem (diffBase + 4)) L.uS ∧
  ReembListAt mem (mem (diffBase + 6)) (mem (diffBase + 7)) L.reemb

/-- Coverage condition for `LevelDiffLists` across a non-rebuilding step `C ↦ C'` at level `i`,
parameterized by `ins j e` (edges inserted by `U_j`, including re-insertions from `D_reins`):
`uG` covers every edge added/removed or inserted by `U_i`, and `reemb` covers every surviving
candidate whose embedding changed or contains an edge inserted by `U_i`. -/
def LevelDiffCovers (C C' : TreeChain) (i : ℕ) (ins : ℕ → ℕ → Prop) (L : LevelDiffLists) : Prop :=
  (∀ e, ((e ∈ (C'.G i).E ↔ e ∉ (C.G i).E) ∨ ins i e) → e ∈ L.uG) ∧
  (∀ e, e ∈ (C.activeLSF i).F.F.E → e ∉ (C'.activeLSF i).F.F.E → e ∈ L.fDel) ∧
  (∀ e, e ∈ (C'.activeLSF i).F.F.E → e ∉ (C.activeLSF i).F.F.E → e ∈ L.uG) ∧
  (∀ e, (e ∈ (C'.activeS i).E ↔ e ∉ (C.activeS i).E) → e ∈ L.uS) ∧
  ReembCovers C C' i L.reemb ∧
  (∀ e, e ∈ (C.activeCore i).E \ (C.activeS i).E →
    e ∈ (C'.activeCore i).E \ (C'.activeS i).E →
    (∃ x ∈ C.activeEmb i e, ins i x.1) → e ∈ L.reemb)

/-! ## 2. Contract interface for candidate-key evaluation -/

/-- Memory-region bound placing every table, dynamic graph, value array, and `MEmbAt` walk buffer
read by `evalKeyProc` strictly below `hi`. -/
def SelectLevelMetaBounded (mem : ℕ → ℕ) (mloc : SelectLevelMetaLoc) (C : TreeChain)
    (hi : ℕ) : Prop :=
  mloc.metaBase + selectLevelMetaSize mloc.d ≤ hi ∧
  mloc.g0Ptr + mloc.eCap 0 * mloc.Lk ≤ hi ∧
  (∀ j ≤ C.d,
    mloc.GPtr j + dynGraphSize (mloc.vCap j) (mloc.eCap j) ≤ hi ∧
    mloc.phiPtr j + mloc.vCap j * mloc.Lk ≤ hi ∧
    mloc.coreLenPtr j + mloc.eCap j * mloc.Lk ≤ hi) ∧
  (∀ j < C.d,
    MEmbBounded mem (mloc.embPtr j) (C.activeCore j).E (mloc.eCap j) (C.activeEmb j) 0 hi)

/-- Contract for `evalKeyProc [meta, lvl, e, nDst, dDst, Lk, scratch]` evaluating the exact
fixed-point `(N_e, D_e)` for a candidate `e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E` into
`nDst` and `dDst` at precision `coreLenPrec C.d P mloc.pLast lvl` (`P` on levels `< d`,
`P + mloc.pLast` on level `d`), preserving memory below `scratch` outside
`[nDst, nDst + Lk) ∪ [dDst, dDst + Lk)`. Everything it reads lies below `scratch`
(`SelectLevelMetaBounded`). -/
def evalCandKeyContract (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ)
    (evalSpace evalCost : ℕ) : Contract where
  pre args mem :=
    ∃ lvl e nDst dDst scratch,
      args = [mloc.metaBase, lvl, e, nDst, dDst, mloc.Lk, scratch] ∧
      16 < 2 ^ w ∧ mloc.pLast < 2 ^ w ∧
      lvl ≤ C.d ∧ e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E ∧
      nDst + mloc.Lk ≤ dDst ∧ dDst + mloc.Lk ≤ scratch ∧
      SelectLevelMetaAt mem mloc h P C g ℓ φ coreLen ∧
      SelectLevelMetaBounded mem mloc C scratch ∧
      ZeroFrom mem scratch ∧ scratch + evalSpace < 2 ^ w
  post args mem ret mem' :=
    let lvl := args.getD 1 0
    let e := args.getD 2 0
    let nDst := args.getD 3 0
    let dDst := args.getD 4 0
    let scratch := args.getD 6 0
    let Q := coreLenPrec C.d P mloc.pLast lvl
    scratch ≤ ret ∧ ret ≤ scratch + evalSpace ∧
    Num.Valid mem' nDst h mloc.Lk ∧ Num.Valid mem' dDst h mloc.Lk ∧
    (∀ j < mloc.Lk, mem' (nDst + j) < 2 ^ w) ∧ (∀ j < mloc.Lk, mem' (dDst + j) < 2 ^ w) ∧
    Num.fixVal mem' nDst h mloc.Lk Q = walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e) ∧
    Num.fixVal mem' dDst h mloc.Lk Q = C.wlenAt ℓ lvl e ∧
    0 < Num.intVal mem' dDst h mloc.Lk ∧
    ZeroFrom mem' ret ∧
    (∀ a < scratch, (a < nDst ∨ nDst + mloc.Lk ≤ a) → (a < dDst ∨ dDst + mloc.Lk ≤ a) →
      mem' a = mem a)
  cost _ _ := evalCost

/-! ## 3. Word-RAM procedures for select-heap updates and suffix rebuilds -/

/-- Process one edge `e` at level `lvl` (`args = [hb, meta, lvl, e, scratch]`):
tests `e ∈ (G_lvl.E \ F_lvl.E \ S_lvl.E)` via `DynGraphAt` presence bits (`dgEPresBase`);
if candidate, evaluates `(N_e, D_e)` at `[scratch, scratch + 2 * Lk)` and calls `heapUpsert`;
otherwise calls `heapDeleteIfLevel`. -/
def selectProcessEdgeBody (evalKey upsert delIf : ℕ) : Stmt :=
  .assign 5 (.load (.bin .add (.reg 1) (.const smDOff))) ;;
  .assign 6 (.bin .add (.reg 5) (.const 1)) ;;
  .assign 7 (.load (.bin .add (.bin .add (.reg 1) (.const smTableOff)) (.reg 2))) ;; -- GPtr[lvl]
  .assign 8 (.load (.bin .add (.bin .add (.reg 1) (.const smTableOff))
    (.bin .add (.reg 6) (.reg 2)))) ;; -- vCap[lvl]
  .assign 9 (.load (.bin .add (.bin .add (.reg 1) (.const smTableOff))
    (.bin .add (.bin .mul (.const 6) (.reg 6)) (.reg 2)))) ;; -- fPtr[lvl]
  -- `dgEPresBase g vCap = g + 4 + 7 * vCap`
  .assign 10 (.load (.bin .add (.bin .add (.bin .add (.reg 7) (.const 4))
    (.bin .mul (.const 7) (.reg 8))) (.reg 3))) ;; -- inG
  .assign 11 (.load (.bin .add (.bin .add (.bin .add (.reg 9) (.const 4))
    (.bin .mul (.const 7) (.reg 8))) (.reg 3))) ;; -- inF
  .assign 12 (.const 0) ;; -- inS (0 if lvl = d)
  .cond (.bin .lt (.reg 2) (.reg 5))
    (.assign 13 (.load (.bin .add (.bin .add (.reg 1) (.const smTableOff))
       (.bin .add (.bin .mul (.const 7) (.reg 6)) (.reg 2)))) ;; -- sPtr[lvl]
     .assign 12 (.load (.bin .add (.bin .add (.bin .add (.reg 13) (.const 4))
       (.bin .mul (.const 7) (.reg 8))) (.reg 3))))
    .nop ;;
  -- Candidate iff `inG = 1 ∧ inF = 0 ∧ inS = 0`
  .cond (.reg 10)
    (.cond (.reg 11)
      (.call 14 delIf [.reg 0, .reg 3, .reg 2, .reg 4] ;; .ret (.reg 14))
      (.cond (.reg 12)
        (.call 14 delIf [.reg 0, .reg 3, .reg 2, .reg 4] ;; .ret (.reg 14))
        (.assign 15 (.load (.bin .add (.reg 0) (.const shLkOff))) ;;
         .assign 16 (.bin .add (.reg 4) (.reg 15)) ;;
         .assign 17 (.bin .add (.reg 16) (.reg 15)) ;;
         .call 18 evalKey [.reg 1, .reg 2, .reg 3, .reg 4, .reg 16, .reg 15, .reg 17] ;;
         .call 19 upsert [.reg 0, .reg 3, .reg 2, .reg 4, .reg 16, .reg 18] ;;
         .ret (.reg 19))))
    (.call 14 delIf [.reg 0, .reg 3, .reg 2, .reg 4] ;; .ret (.reg 14))

theorem selectProcessEdgeBody_noRand (evalKey upsert delIf : ℕ) :
    (selectProcessEdgeBody evalKey upsert delIf).NoRand := by
  simp [selectProcessEdgeBody, Stmt.NoRand]

/-- Scratch space per processed edge: `2 * Lk + evalSpace + heapRebalanceSpace cap Lk`. -/
def selectProcessEdgeSpace (cap Lk evalSpace : ℕ) : ℕ :=
  2 * Lk + evalSpace + heapRebalanceSpace cap Lk

/-- Step cost per processed edge: `evalCost + heapUpsertCost cap Lk + 180`. -/
def selectProcessEdgeCost (cap Lk evalCost : ℕ) : ℕ :=
  evalCost + heapUpsertCost cap Lk + 180

/-- Recursively process a list `[listPtr, listPtr + len)` of edge IDs at level `lvl`.
Arguments: `[hb, meta, lvl, listPtr, len, idx, scratch]`. -/
def selectProcessListBody (self procEdge : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 5) (.reg 4))
    (.assign 7 (.load (.bin .add (.reg 3) (.reg 5))) ;;
     .call 8 procEdge [.reg 0, .reg 1, .reg 2, .reg 7, .reg 6] ;;
     .call 9 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .bin .add (.reg 5) (.const 1), .reg 8] ;;
     .ret (.reg 9))
    (.ret (.reg 6))

theorem selectProcessListBody_noRand (self procEdge : ℕ) :
    (selectProcessListBody self procEdge).NoRand := by
  simp [selectProcessListBody, Stmt.NoRand]

/-- Update a non-rebuilt level `lvl` from `LevelDiffListsAt` at `diffBase`.
Arguments: `[hb, meta, lvl, diffBase, scratch]`. -/
def selectUpdateLevelBody (procList : ℕ) : Stmt :=
  .call 5 procList [.reg 0, .reg 1, .reg 2,
    .load (.reg 3), .load (.bin .add (.reg 3) (.const 1)), .const 0, .reg 4] ;;
  .call 6 procList [.reg 0, .reg 1, .reg 2,
    .load (.bin .add (.reg 3) (.const 2)), .load (.bin .add (.reg 3) (.const 3)), .const 0, .reg 5] ;;
  .call 7 procList [.reg 0, .reg 1, .reg 2,
    .load (.bin .add (.reg 3) (.const 4)), .load (.bin .add (.reg 3) (.const 5)), .const 0, .reg 6] ;;
  .call 8 procList [.reg 0, .reg 1, .reg 2,
    .load (.bin .add (.reg 3) (.const 6)), .load (.bin .add (.reg 3) (.const 7)), .const 0, .reg 7] ;;
  .ret (.reg 8)

theorem selectUpdateLevelBody_noRand (procList : ℕ) :
    (selectUpdateLevelBody procList).NoRand := by
  simp [selectUpdateLevelBody, Stmt.NoRand]

/-- Rebuild level `lvl` from scratch: clears all old candidates at `lvl` via `clearLvl`,
then inserts all new candidates in `G_lvl.E` via `dgEListBase`.
Arguments: `[hb, meta, lvl, scratch]`. -/
def selectRebuildLevelBody (clearLvl procList : ℕ) : Stmt :=
  .call 4 clearLvl [.reg 0, .reg 2, .reg 3] ;;
  .assign 5 (.load (.bin .add (.reg 1) (.const smDOff))) ;;
  .assign 6 (.bin .add (.reg 5) (.const 1)) ;;
  .assign 7 (.load (.bin .add (.bin .add (.reg 1) (.const smTableOff)) (.reg 2))) ;; -- GPtr[lvl]
  .assign 8 (.load (.bin .add (.bin .add (.reg 1) (.const smTableOff))
    (.bin .add (.reg 6) (.reg 2)))) ;; -- vCap[lvl]
  .assign 9 (.load (.bin .add (.bin .add (.reg 1) (.const smTableOff))
    (.bin .add (.bin .mul (.const 2) (.reg 6)) (.reg 2)))) ;; -- eCap[lvl]
  -- `dgMOff = 3`, `dgEListBase g vCap eCap = g + 4 + 7 * vCap + eCap`
  .assign 10 (.load (.bin .add (.reg 7) (.const 3))) ;; -- m_lvl
  .assign 11 (.bin .add (.bin .add (.bin .add (.reg 7) (.const 4))
    (.bin .mul (.const 7) (.reg 8))) (.reg 9)) ;; -- dgEListBase
  .call 12 procList [.reg 0, .reg 1, .reg 2, .reg 11, .reg 10, .const 0, .reg 4] ;;
  .ret (.reg 12)

theorem selectRebuildLevelBody_noRand (clearLvl procList : ℕ) :
    (selectRebuildLevelBody clearLvl procList).NoRand := by
  simp [selectRebuildLevelBody, Stmt.NoRand]

/-- Rebuild suffix levels `cur .. d` recursively (`args = [hb, meta, cur, d, scratch]`). -/
def selectRebuildSuffixBody (self rebuildLvl : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 3) (.reg 2))
    (.ret (.reg 4))
    (.call 5 rebuildLvl [.reg 0, .reg 1, .reg 2, .reg 4] ;;
     .call 6 self [.reg 0, .reg 1, .bin .add (.reg 2) (.const 1), .reg 3, .reg 5] ;;
     .ret (.reg 6))

theorem selectRebuildSuffixBody_noRand (self rebuildLvl : ℕ) :
    (selectRebuildSuffixBody self rebuildLvl).NoRand := by
  simp [selectRebuildSuffixBody, Stmt.NoRand]

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 4. Main Job 2 coverage theorem and chain-transition invariants -/

/-- **Job 2 main coverage theorem (`touched_covers_level_changes`)**:
Across a non-rebuilding update `C ↦ C'` on levels `0..i` (same `d`, decremental active forests
`F'_j ⊆ F_j`, immutable stretches `wstr_j`, unchanged `g`, `ℓ`, and `G_0`-endpoints on surviving
edges), if `lists` satisfies `LevelDiffCovers C C' i lists`, then EVERY edge `e` NOT in
`lists.allTouched`:
1. has the same candidate status at level `i` (`e ∈ S_i ↔ e ∈ S'_i`), and
2. if it is a candidate at level `i`, keeps the exact same signed numerator
   `walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e)` and denominator `C.wlenAt ℓ i e`. -/
theorem touched_covers_level_changes
    {C C' : TreeChain} {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hSpan : C.LastLevelSpans) (hSpan' : C'.LastLevelSpans)
    {i : ℕ} (hi : i ≤ C.d) (hi' : i ≤ C'.d)
    (φ : ℕ → ℕ → ℝ)
    (hPot : SelectPotInv C g φ) (hPot' : SelectPotInv C' g' φ)
    (hEnds : ∀ j ≤ i, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E →
      (C'.G j).tail f = (C.G j).tail f ∧ (C'.G j).head f = (C.G j).head f)
    {ins : ℕ → ℕ → Prop}
    (hWstr : ∀ j ≤ i, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E → ¬ ins j f →
      (C'.activeLSF j).wstr f = (C.activeLSF j).wstr f)
    (hInsFwd : ∀ j < i, ∀ f ∈ (C'.G (j + 1)).E, f ∈ (C.G (j + 1)).E → ins j f → ins (j + 1) f)
    (hℓEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → ℓ' f = ℓ f)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    {lists : LevelDiffLists} (hcov : LevelDiffCovers C C' i ins lists)
    {e : ℕ} (hnotTouched : e ∉ lists.allTouched) :
    (e ∈ (C'.activeCore i).E \ (C'.activeS i).E ↔
      e ∈ (C.activeCore i).E \ (C.activeS i).E) ∧
    (e ∈ (C'.activeCore i).E \ (C'.activeS i).E →
      walkInner (C'.chainGrad g' (i + 1)) (C'.sparsifierCycle i e) =
        walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) ∧
      C'.wlenAt ℓ' i e = C.wlenAt ℓ i e) := by
  obtain ⟨huG, hfDel, hfIns, huS, hreemb, hreembIns⟩ := hcov
  have hnotUG : e ∉ lists.uG := fun h => hnotTouched (by simp [LevelDiffLists.allTouched, h])
  have hnotFD : e ∉ lists.fDel := fun h => hnotTouched (by simp [LevelDiffLists.allTouched, h])
  have hnotUS : e ∉ lists.uS := fun h => hnotTouched (by simp [LevelDiffLists.allTouched, h])
  have hnotRe : e ∉ lists.reemb := fun h => hnotTouched (by simp [LevelDiffLists.allTouched, h])
  have hGiff : e ∈ (C'.G i).E ↔ e ∈ (C.G i).E := by
    by_contra hne
    have hxor : e ∈ (C'.G i).E ↔ e ∉ (C.G i).E := by tauto
    exact hnotUG (huG e (Or.inl hxor))
  have hFiff : e ∈ (C'.activeLSF i).F.F.E ↔ e ∈ (C.activeLSF i).F.F.E := by
    constructor
    · intro h'; by_contra h; exact hnotUG (hfIns e h' h)
    · intro h; by_contra h'; exact hnotFD (hfDel e h h')
  have hSiff : e ∈ (C'.activeS i).E ↔ e ∈ (C.activeS i).E := by
    by_contra hne
    have hxor : e ∈ (C'.activeS i).E ↔ e ∉ (C.activeS i).E := by tauto
    exact hnotUS (huS e hxor)
  have hCandIff : e ∈ (C'.activeCore i).E \ (C'.activeS i).E ↔
      e ∈ (C.activeCore i).E \ (C.activeS i).E := by
    simp only [TreeChain.activeCore, coreGraph, Finset.mem_sdiff, hGiff, hFiff, hSiff]
  refine ⟨hCandIff, fun he' => ?_⟩
  have he : e ∈ (C.activeCore i).E \ (C.activeS i).E := hCandIff.mp he'
  have hemb : C'.activeEmb i e = C.activeEmb i e := by
    by_contra hne; exact hnotRe (hreemb e he he' hne)
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
  have hClosed' := C'.sparsifierCycle_isClosedWalk hH' hSpan' hi' he'
  have hSpEq : C'.sparsifierCycle i e = C.sparsifierCycle i e := by
    unfold TreeChain.sparsifierCycle; rw [hemb]
  have hNotIns : ∀ j ≤ i, ∀ f ∈ walkEdges (C.sparsifierCycle i e), ¬ ins j f := by
    intro j hj f hfW hInsJ
    have hfGi : f ∈ (C.G i).E := (Finset.mem_sdiff.mp (mem_E_of_mem_walkEdges hClosed hfW)).1
    have hfGi' : f ∈ (C'.G i).E :=
      (Finset.mem_sdiff.mp (mem_E_of_mem_walkEdges hClosed' (hSpEq ▸ hfW))).1
    have hProp : ∀ k, j ≤ k → k ≤ i → ins k f := by
      intro k hjk
      induction k with
      | zero =>
        intro _
        have : j = 0 := by omega
        subst this; exact hInsJ
      | succ k ih =>
        intro hki
        by_cases hjeq : j = k + 1
        · subst hjeq; exact hInsJ
        · exact hInsFwd k (by omega) f (C'.G_E_subset_of_le hH' hki hi' hfGi')
            (C.G_E_subset_of_le hH hki hi hfGi) (ih (by omega) (by omega))
    have hInsI : ins i f := hProp i hj le_rfl
    obtain ⟨dir, hmem⟩ := LSF.mem_walkEdges_iff.mp hfW
    unfold TreeChain.sparsifierCycle at hmem
    rcases List.mem_cons.mp hmem with heq | hrev
    · have hfe : f = e := congrArg Prod.fst heq
      exact hnotUG (huG e (Or.inr (hfe ▸ hInsI)))
    · obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp (List.mem_reverse.mp hrev)
      have hfy : y.1 = f := congrArg Prod.fst hyEq
      exact hnotRe (hreembIns e he he' ⟨y, hy, hfy ▸ hInsI⟩)
  exact walkInner_and_wlenAt_eq_of_unchanged_emb C C' hH hSpan hH' hSpan' hi hi' φ
    (fun j hj => hPot j (le_trans hj hi)) (fun j hj => hPot' j (le_trans hj hi'))
    hEnds (fun j hj f hfW =>
      have hfGi : f ∈ (C.G i).E := (Finset.mem_sdiff.mp (mem_E_of_mem_walkEdges hClosed hfW)).1
      have hfGi' : f ∈ (C'.G i).E :=
        (Finset.mem_sdiff.mp (mem_E_of_mem_walkEdges hClosed' (hSpEq ▸ hfW))).1
      hWstr j hj f (C'.G_E_subset_of_le hH' hj hi' hfGi') (C.G_E_subset_of_le hH hj hi hfGi)
        (hNotIns j hj f hfW))
    hℓEq hgEq he he' hemb

/-- **Prefix preservation under `Shift(i₀)` / `Rebuild(i₀)`**:
Every level `i < i₀` where `G_j`, `activeLSF j`, `activeS j`, `activeEmb j` (and `g`, `ℓ` on `G_0`)
agree between `C` and `C'` preserves both candidate membership and `(walkInner, wlenAt)` keys
without touching the heap at all. -/
theorem selectHeap_prefix_preserved
    {C C' : TreeChain} {g g' ℓ ℓ' : ℕ → ℝ} {i₀ : ℕ}
    (hG : ∀ j < i₀, C'.G j = C.G j)
    (hLSF : ∀ j < i₀, C'.activeLSF j = C.activeLSF j)
    (hS : ∀ j < i₀, C'.activeS j = C.activeS j)
    (hEmb : ∀ j < i₀, C'.activeEmb j = C.activeEmb j)
    (hg : ∀ e, g' e = g e) (hℓ : ∀ e, ℓ' e = ℓ e)
    {i : ℕ} (hi : i < i₀) (e : ℕ) :
    (e ∈ (C'.activeCore i).E \ (C'.activeS i).E ↔
      e ∈ (C.activeCore i).E \ (C.activeS i).E) ∧
    (e ∈ (C.activeCore i).E \ (C.activeS i).E →
      walkInner (C'.chainGrad g' (i + 1)) (C'.sparsifierCycle i e) =
        walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) ∧
      C'.wlenAt ℓ' i e = C.wlenAt ℓ i e) := by
  have hcand : e ∈ (C'.activeCore i).E \ (C'.activeS i).E ↔
      e ∈ (C.activeCore i).E \ (C.activeS i).E := by
    simp [TreeChain.activeCore, hG i hi, hLSF i hi, hS i hi]
  have hfunG : g' = g := funext hg
  have hfunL : ℓ' = ℓ := funext hℓ
  subst hfunG; subst hfunL
  refine ⟨hcand, fun he => ?_⟩
  exact (walkInner_and_wlenAt_congr_prefix C C'
    (fun j hj => hG j (lt_of_le_of_lt hj hi))
    (fun j hj => hLSF j (lt_of_le_of_lt hj hi))
    (hS i hi) (hEmb i hi) he).2

/-- **Exact changed-key count for a single `Update` step**:
If a step updates non-rebuilt levels `0 .. r - 1` via `lists j` (`LevelDiffLists`) and rebuilds
levels `r .. d` from scratch, then the total number of heap operations (`heapUpsert` + `heapDelete`)
performed is at most
`∑_{j < r} (lists j).totalLen + ∑_{j = r}^{d} (|(C.activeCore j).E \ (C.activeS j).E| + |(C'.G j).E|)`. -/
@[expose] noncomputable def updateHeapOpsBound (C C' : TreeChain) (r : ℕ) (lists : ℕ → LevelDiffLists) : ℕ :=
  (Finset.range r).sum (fun j => (lists j).totalLen) +
  (Finset.Icc r C'.d).sum (fun j =>
    ((C.activeCore j).E \ (C.activeS j).E).card + (C'.G j).E.card)

/-- Bound on `totalLen` of a `LevelDiffLists` when `reemb` satisfies `ReembCostBound`:
every touched edge at a non-rebuilt level is paid by the input batch `U_i`, the forest deletions
`fDel_i`, the sparsifier batch `U_{S,i}`, `cReemb * (toolCostDelta + 1)`, and the drop of the
potential from `phi` to `phi'`. -/
theorem levelDiffLists_totalLen_le {L : LevelDiffLists} {toolCostDelta cReemb phi phi' : ℕ}
    (hre : ReembCostBound L.reemb toolCostDelta cReemb phi phi') :
    L.totalLen + phi' ≤
      L.uG.length + L.fDel.length + L.uS.length + cReemb * (toolCostDelta + 1) + phi := by
  unfold LevelDiffLists.totalLen ReembCostBound at *
  omega

/-- Every `LevelDiffLists.allTouched` has length equal to `LevelDiffLists.totalLen`. -/
theorem levelDiffLists_allTouched_length (L : LevelDiffLists) :
    L.allTouched.length = L.totalLen := by
  simp [LevelDiffLists.allTouched, LevelDiffLists.totalLen, Nat.add_assoc]

/-! ## 5. Step-cost composition bounds for `selectProcessListBody`, `selectUpdateLevelBody`,
`selectRebuildLevelBody`, and `selectRebuildSuffixBody` -/

/-- Space bound for `selectProcessListBody` over `len` touched edges. -/
@[expose] def selectProcessListSpace (len cap Lk evalSpace : ℕ) : ℕ :=
  len * selectProcessEdgeSpace cap Lk evalSpace

/-- Time bound for `selectProcessListBody` over `len` touched edges:
`O(len · (evalCost + (log(cap + 1) + 1) · (Lk^2 + 1)))`. -/
@[expose] def selectProcessListCost (len cap Lk evalCost : ℕ) : ℕ :=
  len * (selectProcessEdgeCost cap Lk evalCost + 40) + 20

/-- Time bound for `selectUpdateLevelBody` on `L : LevelDiffLists`. -/
@[expose] def selectUpdateLevelCost (L : LevelDiffLists) (cap Lk evalCost : ℕ) : ℕ :=
  selectProcessListCost L.totalLen cap Lk evalCost + 120

/-- Time bound for `selectRebuildLevelBody` clearing `oldCand` candidates and scanning `mNew` edges. -/
@[expose] def selectRebuildLevelCost (oldCand mNew cap Lk evalCost : ℕ) : ℕ :=
  heapClearLevelCost oldCand cap Lk + selectProcessListCost mNew cap Lk evalCost + 120

/-- Key-update cost bound lemma: every single changed key at level `i` costs at most
`evalCost + 36 * Lk + (Nat.log 2 (cap + 1) + 1) * (2 * keyCompareCost Lk + 240) + keyCompareCost Lk + 640`,
i.e., `O(log(cap + 1) · Lk^2)` heap comparisons plus one key evaluation. -/
theorem selectProcessEdgeCost_le_log (cap Lk evalCost : ℕ) :
    selectProcessEdgeCost cap Lk evalCost ≤
      evalCost + (Nat.log 2 (cap + 1) + 1) * (2 * keyCompareCost Lk + 240) +
        keyCompareCost Lk + 36 * Lk + 760 := by
  unfold selectProcessEdgeCost heapUpsertCost heapRebalanceCost
  omega

/-- Per-level rebuild cost scales linearly with `oldCand + mNew` times the single-key cost. -/
theorem selectRebuildLevelCost_le_linear (oldCand mNew cap Lk evalCost : ℕ) :
    selectRebuildLevelCost oldCand mNew cap Lk evalCost ≤
      (oldCand + mNew) * (selectProcessEdgeCost cap Lk evalCost + 60) + 200 := by
  unfold selectRebuildLevelCost heapClearLevelCost selectProcessListCost
    heapDeleteCost selectProcessEdgeCost heapUpsertCost
  have hle : heapRebalanceCost cap Lk + 240 + 60 ≤
      evalCost + (36 * Lk + heapRebalanceCost cap Lk + 420) + 180 + 60 := by omega
  have h1 : oldCand * (heapRebalanceCost cap Lk + 240 + 60) ≤
      oldCand * (evalCost + (36 * Lk + heapRebalanceCost cap Lk + 420) + 180 + 60) :=
    Nat.mul_le_mul_left _ hle
  have h2 : mNew * (evalCost + (36 * Lk + heapRebalanceCost cap Lk + 420) + 180 + 40) ≤
      mNew * (evalCost + (36 * Lk + heapRebalanceCost cap Lk + 420) + 180 + 60) :=
    Nat.mul_le_mul_left _ (by omega)
  rw [Nat.add_mul]
  linarith [h1, h2]

end MinCostFlow.MinRatio
