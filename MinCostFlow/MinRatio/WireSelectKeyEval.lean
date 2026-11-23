module

public import MinCostFlow.MinRatio.WireSelectHeapClear
public import MinCostFlow.Num.Add
public import MinCostFlow.Num.Subtract
public import MinCostFlow.Num.Equal
public import MinCostFlow.DynSpanner.Program.DynGraphLayout
public import MinCostFlow.DynSpanner.Program.EmbLayouts
import WordRAM.Tactic

/-!
# Per-level key-evaluation metadata, frozen-potential gradient, and exact core-length update

Implements the first half of key evaluation for the select-heap (`jtree.tex`, pages 21 and 24):
1. `SelectLevelMetaLoc` and `SelectLevelMetaAt`: contiguous metadata table storing per-level
   pointers to `G_j` (`DynGraphAt`), frozen vertex potentials `φ_j`, exact core lengths
   `coreLen_j = chainLen ℓ (j + 1)` (the lengths of the core graph of level `j`), embeddings `activeEmb j` (`MEmbAt`), active forests `F_j`, active
   sparsifiers `S_j`, and the base gradient table `g0Ptr`.
2. `SelectPotInv` and `SelectCoreLenInv`, with pure correctness bridges:
   - `selectPotInv_frozen_from_init` (frozen `treeRootPot L_j.T gInit_j` matches `potGrad` on
     every surviving forest path of `F_j`),
   - `selectCoreLenInv_step_exact` (exact division-free core-length update via
     `stretch_coreLen_exact`),
   - `walkLength_eq_net_count_sum` (exact multiplicity aggregation over packed `(2 * f + dirBit)`).
3. Verified deterministic Word-RAM procedures:
   - `updateCoreLenEdgeBody` (`[prevPtr, numPtr, denPtr, dstPtr, L]`): computes
     `if num == den then prev else num` in `O(L)` steps.
   - `evalEdgePotGradBody` (`[meta, lvl, f, dstPtr, Lk, scratch]`): computes
     `potGrad C g φ (lvl + 1) f` in `O((lvl + 1) · Lk)` steps.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 1. Per-level metadata layout `SelectLevelMetaLoc` -/

/-- Header offsets inside the select-heap metadata block at `meta`.
The 8 per-level arrays each have length `d + 1` starting at `meta + 2`:
- block 0: `GPtr[0..d]`
- block 1: `vCap[0..d]`
- block 2: `eCap[0..d]`
- block 3: `phiPtr[0..d]`
- block 4: `coreLenPtr[0..d]`
- block 5: `embPtr[0..d]` (entries `0..d-1` hold `MEmbAt` pointers)
- block 6: `fPtr[0..d]`
- block 7: `sPtr[0..d]` (entries `0..d-1` hold `DynGraphAt` pointers for `activeS j`) -/
def smG0Off : ℕ := 0
def smDOff : ℕ := 1
def smTableOff : ℕ := 2

/-- Address of per-level array `blk ∈ {0..7}`, level `j ≤ d`, inside metadata block `metaBase`. -/
def smEntryAddr (metaBase d blk j : ℕ) : ℕ :=
  metaBase + smTableOff + blk * (d + 1) + j

/-- Total word size of a select-level metadata block for depth `d`. -/
def selectLevelMetaSize (d : ℕ) : ℕ :=
  2 + 8 * (d + 1)

/-- Fixed-point precision of the stored core-length table at level `j` of a depth-`d` chain:
`P` on interior levels `j < d`, and `P + pLast` on the terminal level `j = d` (where rounded
last-level stretches live on the `2 ^ (-pLast)` grid). -/
def coreLenPrec (d P pLast j : ℕ) : ℕ :=
  if j < d then P else P + pLast

/-- Concrete per-level metadata descriptor for a tree chain of depth `d`.
The unused terminal slot `sPtr d` stores `pLast`, the stretch-rounding precision of level `d`. -/
structure SelectLevelMetaLoc where
  metaBase : ℕ
  d : ℕ
  Lk : ℕ
  g0Ptr : ℕ
  GPtr : ℕ → ℕ
  vCap : ℕ → ℕ
  eCap : ℕ → ℕ
  phiPtr : ℕ → ℕ
  coreLenPtr : ℕ → ℕ
  embPtr : ℕ → ℕ
  fPtr : ℕ → ℕ
  sPtr : ℕ → ℕ
  pLast : ℕ := 0

/-- Frozen-potential invariant: on every level `j ≤ C.d`, `φ j` matches `potGrad C g φ j`
along every path of the active forest `(C.activeLSF j).F.F`. -/
def SelectPotInv (C : TreeChain) (g : ℕ → ℝ) (φ : ℕ → ℕ → ℝ) : Prop :=
  ∀ j ≤ C.d, ∀ a b, (C.activeLSF j).F.F.Connected a b →
    walkInner (potGrad C g φ j) ((C.activeLSF j).F.F.forestPath a b) = φ j a - φ j b

/-- Exact core-length invariant: on every level `j ≤ C.d`, `coreLen j` equals
`C.chainLen ℓ (j + 1)` on `(C.G j).E`. These are the lengths of the core graph of level `j`, so the
key of a candidate at level `j` reads them (`C.wlenAt ℓ j e` is a walk length in
`C.chainLen ℓ (j + 1)`). -/
def SelectCoreLenInv (C : TreeChain) (ℓ : ℕ → ℝ) (coreLen : ℕ → ℕ → ℝ) : Prop :=
  ∀ j ≤ C.d, ∀ e ∈ (C.G j).E, coreLen j e = C.chainLen ℓ (j + 1) e

/-- Memory invariant for the select-level metadata block `mloc` representing chain `C` with
base gradient `g`, base length `ℓ`, frozen potentials `φ`, and exact core lengths `coreLen`
at limb bit-width `h`, limb count `mloc.Lk`, and fixed-point precision `P`. -/
def SelectLevelMetaAt (mem : ℕ → ℕ) (mloc : SelectLevelMetaLoc) (h P : ℕ)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ) : Prop :=
  mloc.d = C.d ∧
  mem (mloc.metaBase + smG0Off) = mloc.g0Ptr ∧
  mem (mloc.metaBase + smDOff) = mloc.d ∧
  (∀ j ≤ C.d,
    mem (smEntryAddr mloc.metaBase mloc.d 0 j) = mloc.GPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 1 j) = mloc.vCap j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 2 j) = mloc.eCap j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 3 j) = mloc.phiPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 4 j) = mloc.coreLenPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 5 j) = mloc.embPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 6 j) = mloc.fPtr j ∧
    mem (smEntryAddr mloc.metaBase mloc.d 7 j) = mloc.sPtr j) ∧
  EdgeValuesAt mem mloc.g0Ptr h mloc.Lk P (C.G 0).E g ∧
  (∀ j ≤ C.d, DynGraphAt mem (mloc.GPtr j) (mloc.vCap j) (mloc.eCap j) (C.G j)) ∧
  (∀ j ≤ C.d, EdgeValuesAt mem (mloc.phiPtr j) h mloc.Lk P (C.G j).V (φ j)) ∧
  (∀ j ≤ C.d, EdgeValuesAt mem (mloc.coreLenPtr j) h mloc.Lk
    (coreLenPrec C.d P mloc.pLast j) (C.G j).E (coreLen j)) ∧
  (∀ j < C.d, MEmbAt mem (mloc.embPtr j) (C.activeCore j).E (mloc.eCap j) (C.activeEmb j)) ∧
  (∀ j ≤ C.d, DynGraphAt mem (mloc.fPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeLSF j).F.F) ∧
  (∀ j < C.d, DynGraphAt mem (mloc.sPtr j) (mloc.vCap j) (mloc.eCap j) (C.activeS j)) ∧
  SelectPotInv C g φ ∧
  SelectCoreLenInv C ℓ coreLen ∧
  mloc.sPtr mloc.d = mloc.pLast

/-! ## 2. `updateCoreLenEdgeBody`: exact division-free core-length update -/

/-- Exact core-length update for one edge: given `[prevPtr, numPtr, denPtr, dstPtr, L]`,
tests `num == den` via `eqProc` and copies `prevPtr` (if equal) or `numPtr` (otherwise) into
`dstPtr` via `copyTo`. -/
def updateCoreLenEdgeBody (eqProc copyTo : ℕ) : Stmt :=
  .call 5 eqProc [.reg 1, .reg 2, .reg 4] ;;
  .cond (.reg 5)
    (.call 6 copyTo [.reg 0, .reg 3, .reg 4] ;; .ret (.const 0))
    (.call 6 copyTo [.reg 1, .reg 3, .reg 4] ;; .ret (.const 0))

theorem updateCoreLenEdgeBody_noRand (eqProc copyTo : ℕ) :
    (updateCoreLenEdgeBody eqProc copyTo).NoRand := by
  simp [updateCoreLenEdgeBody, Stmt.NoRand]

/-- Step cost bound for `updateCoreLenEdgeBody`: `41 * L + 60`. -/
def updateCoreLenEdgeCost (L : ℕ) : ℕ := 41 * L + 60

/-- Contract for `updateCoreLenEdgeBody`: writes exact `wstr * prev` into `dstPtr` when
`den = prev ∨ num = den`, using zero scratch memory. -/
def updateCoreLenEdgeContract (w h P : ℕ) : Contract where
  pre args mem :=
    ∃ prevPtr numPtr denPtr dstPtr L,
      args = [prevPtr, numPtr, denPtr, dstPtr, L] ∧
      1 < 2 ^ w ∧
      prevPtr + L < 2 ^ w ∧ numPtr + L < 2 ^ w ∧ denPtr + L < 2 ^ w ∧ dstPtr + L < 2 ^ w ∧
      (prevPtr + L ≤ dstPtr ∨ dstPtr + L ≤ prevPtr) ∧
      (numPtr + L ≤ dstPtr ∨ dstPtr + L ≤ numPtr) ∧
      Num.Valid mem prevPtr h L ∧ Num.Valid mem numPtr h L ∧ Num.Valid mem denPtr h L ∧
      (∀ i < L, mem (prevPtr + i) < 2 ^ w) ∧ (∀ i < L, mem (numPtr + i) < 2 ^ w) ∧
      0 < Num.fixVal mem denPtr h L P ∧
      (Num.fixVal mem denPtr h L P = Num.fixVal mem prevPtr h L P ∨
        Num.fixVal mem numPtr h L P = Num.fixVal mem denPtr h L P)
  post args mem ret mem' :=
    let prevPtr := args.getD 0 0
    let numPtr := args.getD 1 0
    let denPtr := args.getD 2 0
    let dstPtr := args.getD 3 0
    let L := args.getD 4 0
    ret = 0 ∧
    Num.Valid mem' dstPtr h L ∧
    Num.fixVal mem' dstPtr h L P =
      (Num.fixVal mem numPtr h L P / Num.fixVal mem denPtr h L P) *
        Num.fixVal mem prevPtr h L P ∧
    (∀ a, (a < dstPtr ∨ dstPtr + L ≤ a) → mem' a = mem a)
  cost args _ := updateCoreLenEdgeCost (args.getD 4 0)

/-! ## 3. `evalEdgePotGradBody`: `O((lvl + 1) · Lk)` evaluation of `potGrad C g φ (lvl + 1) f` -/

/-- Recursive loop helper for `evalEdgePotGradBody`: adds `φ[j][head_j(f)] - φ[j][tail_j(f)]`
for levels `j = cur .. lvl` into `dstPtr` (`Lk` limbs), returning the final scratch pointer.
Arguments: `[meta, lvl, f, dstPtr, Lk, cur, scratch]`. -/
def evalEdgePotGradLoopBody (self copyTo addProc subProc : ℕ) : Stmt :=
  .cond (.bin .lt (.reg 1) (.reg 5))
    (.ret (.reg 6))
    (.assign 7 (.load (.bin .add (.reg 0) (.const smDOff))) ;;
     .assign 8 (.bin .add (.reg 7) (.const 1)) ;;
     .assign 9 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff)) (.reg 5))) ;; -- GPtr[cur]
     .assign 10 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff))
       (.bin .add (.reg 8) (.reg 5)))) ;; -- vCap[cur]
     .assign 11 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff))
       (.bin .add (.bin .mul (.const 2) (.reg 8)) (.reg 5)))) ;; -- eCap[cur]
     .assign 12 (.load (.bin .add (.bin .add (.reg 0) (.const smTableOff))
       (.bin .add (.bin .mul (.const 3) (.reg 8)) (.reg 5)))) ;; -- phiPtr[cur]
     -- `dgIntToExtBase g vCap = g + 4 + 4 * vCap`
     -- `dgETailSlotBase g vCap eCap = g + 4 + 7 * vCap + 3 * eCap`
     -- `dgEHeadSlotBase g vCap eCap = g + 4 + 7 * vCap + 4 * eCap`
     .assign 13 (.bin .add (.bin .add (.reg 9) (.const 4)) (.bin .mul (.const 4) (.reg 10))) ;;
     .assign 14 (.bin .add (.bin .add (.bin .add (.reg 9) (.const 4))
       (.bin .mul (.const 7) (.reg 10))) (.bin .mul (.const 3) (.reg 11))) ;;
     .assign 15 (.bin .add (.reg 14) (.reg 11)) ;;
     .assign 16 (.load (.bin .add (.reg 13) (.load (.bin .add (.reg 14) (.reg 2))))) ;; -- tail_cur(f)
     .assign 17 (.load (.bin .add (.reg 13) (.load (.bin .add (.reg 15) (.reg 2))))) ;; -- head_cur(f)
     .call 18 addProc [.reg 3, .bin .add (.reg 12) (.bin .mul (.reg 17) (.reg 4)), .reg 4, .reg 6] ;;
     .call 19 subProc [.reg 6, .bin .add (.reg 12) (.bin .mul (.reg 16) (.reg 4)), .reg 4, .reg 18] ;;
     .call 20 copyTo [.bin .add (.reg 18) (.reg 4), .reg 3, .reg 4] ;;
     .call 21 self [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .bin .add (.reg 5) (.const 1), .reg 19] ;;
     .ret (.reg 21))

theorem evalEdgePotGradLoopBody_noRand (self copyTo addProc subProc : ℕ) :
    (evalEdgePotGradLoopBody self copyTo addProc subProc).NoRand := by
  simp [evalEdgePotGradLoopBody, Stmt.NoRand]

/-- Entry procedure `evalEdgePotGradBody` (`[meta, lvl, f, dstPtr, Lk, scratch]`):
copies `g0[f]` into `dstPtr` and calls `loop` from `cur = 0` to `lvl`. -/
def evalEdgePotGradBody (loopProc copyTo : ℕ) : Stmt :=
  .assign 6 (.load (.bin .add (.reg 0) (.const smG0Off))) ;;
  .call 7 copyTo [.bin .add (.reg 6) (.bin .mul (.reg 2) (.reg 4)), .reg 3, .reg 4] ;;
  .call 8 loopProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .const 0, .reg 5] ;;
  .ret (.reg 8)

theorem evalEdgePotGradBody_noRand (loopProc copyTo : ℕ) :
    (evalEdgePotGradBody loopProc copyTo).NoRand := by
  simp [evalEdgePotGradBody, Stmt.NoRand]

/-- Scratch space per level of `evalEdgePotGrad`: `Num.add` uses `Lk`, `Num.subtract` uses `2 * Lk`. -/
def evalEdgePotGradSpace (lvl Lk : ℕ) : ℕ := (lvl + 1) * (3 * Lk)

/-- Step cost bound for `evalEdgePotGradBody`: `O((lvl + 1) · Lk)`. -/
def evalEdgePotGradCost (lvl Lk : ℕ) : ℕ :=
  (lvl + 1) * (130 * Lk + 180) + 18 * Lk + 60

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-! ## 4. Pure mathematical bridges for key evaluation -/

/-- Frozen initialization potentials `φ j = treeRootPot (C.activeLSF j).T (gInit j)` satisfy
`SelectPotInv` whenever `(C.activeLSF j).F.F` is a subgraph of `T` and `gInit j` agrees with
`potGrad C g φ j` on `(C.activeLSF j).F.F.E`. -/
theorem selectPotInv_frozen_from_init {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ gInit : ℕ → ℕ → ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hPhi : ∀ j ≤ C.d, ∀ v ∈ (C.activeLSF j).F.F.V, φ j v = treeRootPot (C.activeLSF j).T (gInit j) v)
    (hAgree : ∀ j ≤ C.d, ∀ e ∈ (C.activeLSF j).F.F.E, gInit j e = potGrad C g φ j e) :
    SelectPotInv C g φ := by
  intro j hj a b hconn
  have h1 := potGrad_treeRootPot_of_agree C hH hj (fun f hf => (hAgree j hj f hf).symm) hconn
  have hRF := (C.activeLSF_holds hH hj).2.1
  by_cases hab : a = b
  · subst hab
    rw [LSF.forestPath_self hRF.1 a]
    simp [walkInner_nil]
  · have hFsub := hRF.2.2.2.2
    have hValF : (C.activeLSF j).F.F.IsValid := fun e he => by
      have hv := C.G_isValid hH j hj e (hFsub.2.1 he)
      rw [hRF.2.1, (hFsub.2.2 e he).1, (hFsub.2.2 e he).2]; exact hv
    have hWalkV : ∀ {u v : ℕ} {W : List (ℕ × Bool)},
        (C.activeLSF j).F.F.IsWalk u v W → u ≠ v →
        u ∈ (C.activeLSF j).F.F.V ∧ v ∈ (C.activeLSF j).F.F.V := by
      intro u v W hW
      induction hW with
      | nil _ => intro hne; exact (hne rfl).elim
      | @cons a c x rest he hsrc hrest ih =>
        intro _
        obtain ⟨e, dir⟩ := x
        have hve := hValF e he
        have ha : a ∈ (C.activeLSF j).F.F.V := by
          cases dir <;> simp_all [MGraph.src]
        have hb : (C.activeLSF j).F.F.dst (e, dir) ∈ (C.activeLSF j).F.F.V := by
          cases dir <;> simp_all [MGraph.dst]
        by_cases hbc : (C.activeLSF j).F.F.dst (e, dir) = c
        · exact ⟨ha, hbc ▸ hb⟩
        · exact ⟨ha, (ih hbc).2⟩
    obtain ⟨W, hW⟩ := hconn
    obtain ⟨haV, hbV⟩ := hWalkV hW hab
    rw [hPhi j hj a haV, hPhi j hj b hbV]
    exact h1

/-- Exact division-free core-length propagation across level `i` using `stretch_coreLen_exact`. -/
theorem selectCoreLenInv_step_exact {C : TreeChain} {ℓ : ℕ → ℝ} {coreLen : ℕ → ℕ → ℝ}
    {i : ℕ}
    (hprev : ∀ e ∈ (C.G i).E, coreLen i e = C.chainLen ℓ i e)
    (hnext : ∀ e ∈ (C.G (i + 1)).E, e ∈ (C.G i).E ∧
      ∃ num den : ℝ, 0 < den ∧ num / den = (C.activeLSF i).wstr e ∧
        (den = coreLen i e ∨ num = den) ∧
        coreLen (i + 1) e = if num = den then coreLen i e else num) :
    ∀ e ∈ (C.G (i + 1)).E, coreLen (i + 1) e = C.chainLen ℓ (i + 1) e := by
  intro e he
  obtain ⟨hePrev, num, den, hden, hquot, hcase, hval⟩ := hnext e he
  rw [hval, stretch_coreLen_exact hden hquot hcase, hprev e hePrev]
  rfl

/-- Exact multiplicity sum for `walkLength` over a walk `W`: grouping steps of `W` by edge ID `f`
and multiplying `ℓ f` by `|#(f, true) - #(f, false)|` yields `walkLength ℓ W`. -/
theorem walkLength_eq_abs_count_diff_sum (ℓ : ℕ → ℝ) (W : List (ℕ × Bool)) :
    walkLength ℓ W =
      ∑ f ∈ walkEdges W,
        ℓ f * (((W.count (f, true) : ℤ) - (W.count (f, false) : ℤ)).natAbs : ℝ) := by
  have hwf : ∀ (V : List (ℕ × Bool)) (f : ℕ),
      walkFlow V f = ((V.count (f, true) : ℤ) - (V.count (f, false) : ℤ) : ℝ) := by
    intro V f
    induction V with
    | nil => simp [walkFlow_nil]
    | cons x xs ih =>
      obtain ⟨e, dir⟩ := x
      rw [walkFlow_cons, ih]
      cases dir <;> by_cases hef : e = f <;> simp [hef] <;> ring
  unfold walkLength
  refine Finset.sum_congr rfl fun f _ => ?_
  congr 1
  rw [hwf W f]
  have hcast : (((W.count (f, true) : ℤ) - (W.count (f, false) : ℤ)).natAbs : ℝ) =
      |(((W.count (f, true) : ℤ) - (W.count (f, false) : ℤ) : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast]
  rw [hcast]
  simp [Int.cast_sub, Int.cast_natCast]

/-- `DynGraphAt` lookup of edge endpoints: reading `dgIntToExtBase[dgETailSlotBase[e]]` recovers
`G.tail e` and `dgIntToExtBase[dgEHeadSlotBase[e]]` recovers `G.head e`. -/
theorem dynGraphAt_read_endpoints {mem : ℕ → ℕ} {a vCap eCap : ℕ} {G : MGraph}
    (hG : DynGraphAt mem a vCap eCap G) {e : ℕ} (he : e ∈ G.E) :
    mem (dgIntToExtBase a vCap + mem (dgETailSlotBase a vCap eCap + e)) = G.tail e ∧
    mem (dgIntToExtBase a vCap + mem (dgEHeadSlotBase a vCap eCap + e)) = G.head e := by
  have hvalid := hG.1 e he
  have hth := hG.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he
  have hbi := hG.2.2.2.2.2.2.2.2.2.1
  exact ⟨by rw [hth.1]; exact (hbi (G.tail e) hvalid.1).2,
         by rw [hth.2]; exact (hbi (G.head e) hvalid.2).2⟩

/-! ## 5. Verification of `updateCoreLenEdgeBody` -/

/-- `updateCoreLenEdgeBody` meets `updateCoreLenEdgeContract` in `O(L)` steps with zero scratch. -/
theorem updateCoreLenEdge_meetsContract {w h P proc eqProc copyTo : ℕ} {p : Program}
    (hp : p.procs[proc]? = some (updateCoreLenEdgeBody eqProc copyTo))
    (heq : MeetsContract w p eqProc (Num.equalContract w h))
    (hcopy : MeetsContract w p copyTo (copyLimbsToContract w)) :
    MeetsContract w p proc (updateCoreLenEdgeContract w h P) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨prevPtr, numPtr, denPtr, dstPtr, L, rfl, hw1, hpW, hnW, hdW, hdstW, hdisjP, hdisjN,
    hvP, hvN, hvD, hpw, hnw, hdenPos, hcase⟩ := hpre
  have hp0W : prevPtr < 2 ^ w := hwords prevPtr (by simp)
  have hn0W : numPtr < 2 ^ w := hwords numPtr (by simp)
  have hd0W : denPtr < 2 ^ w := hwords denPtr (by simp)
  have hdst0W : dstPtr < 2 ^ w := hwords dstPtr (by simp)
  have hLW : L < 2 ^ w := hwords L (by simp)
  apply runs_start_le
  dsimp only [startState]
  unfold updateCoreLenEdgeBody
  refine runs_seq_call_flat heq (vs := [numPtr, denPtr, L]) (by eval_expr) (by wram_words) ?_ ?_
  · exact ⟨numPtr, denPtr, L, rfl, hnW, hdW, hvN, hvD⟩
  · intro bit mem1 pos1 hpEq
    obtain ⟨hmem1, hbit⟩ := hpEq
    change mem1 = mem at hmem1
    subst mem1
    change bit = (if Num.intVal mem numPtr h L = Num.intVal mem denPtr h L then 1 else 0) at hbit
    have hbitW : bit < 2 ^ w := by rw [hbit]; split <;> omega
    have hpowPos : (0 : ℝ) < (2 : ℝ) ^ P := pow_pos zero_lt_two P
    have hfixEqIff : Num.intVal mem numPtr h L = Num.intVal mem denPtr h L ↔
        Num.fixVal mem numPtr h L P = Num.fixVal mem denPtr h L P := by
      unfold Num.fixVal
      constructor
      · intro heq; rw [heq]
      · intro heq
        have h1 : (Num.intVal mem numPtr h L : ℝ) = (Num.intVal mem denPtr h L : ℝ) := by
          have := congrArg (· * (2 : ℝ) ^ P) heq
          simpa [div_mul_cancel₀ _ (ne_of_gt hpowPos)] using this
        exact Int.cast_injective h1
    refine WordRAM.runs_cond_le (v := bit) (by eval_expr) ?_ ?_
    · intro hnz
      have heqInt : Num.intVal mem numPtr h L = Num.intVal mem denPtr h L := by
        by_contra hne; rw [ite_eq_right hne] at hbit; exact hnz hbit
      have heqFix : Num.fixVal mem numPtr h L P = Num.fixVal mem denPtr h L P :=
        hfixEqIff.mp heqInt
      refine runs_seq_call_flat hcopy (vs := [prevPtr, dstPtr, L]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨prevPtr, dstPtr, L, rfl, hw1, hpW, hdstW, hdisjP, hpw⟩
      · intro _ mem2 pos2 hpCp
        obtain ⟨_, hcp, hfr⟩ := hpCp
        change (∀ i < L, mem2 (dstPtr + i) = mem (prevPtr + i)) at hcp
        change (∀ a, (a < dstPtr ∨ dstPtr + L ≤ a) → mem2 a = mem a) at hfr
        refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
        · dsimp only [updateCoreLenEdgeContract]
          simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
          refine ⟨trivial, fun i hi => (hcp i hi) ▸ hvP i hi, ?_, hfr⟩
          have hdstEq : Num.fixVal mem2 dstPtr h L P = Num.fixVal mem prevPtr h L P := by
            unfold Num.fixVal; rw [Num.intVal_congr hcp]
          rw [hdstEq]
          have hst := stretch_coreLen_exact hdenPos rfl hcase
          rw [ite_eq_left heqFix] at hst
          exact hst
        · simp only [updateCoreLenEdgeContract, updateCoreLenEdgeCost, Num.equalContract,
            copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
          omega
    · intro hzBit
      have hneInt : Num.intVal mem numPtr h L ≠ Num.intVal mem denPtr h L := by
        intro heqI; rw [ite_eq_left heqI] at hbit; omega
      have hneFix : Num.fixVal mem numPtr h L P ≠ Num.fixVal mem denPtr h L P :=
        fun hne => hneInt (hfixEqIff.mpr hne)
      refine runs_seq_call_flat hcopy (vs := [numPtr, dstPtr, L]) (by eval_expr) (by wram_words) ?_ ?_
      · exact ⟨numPtr, dstPtr, L, rfl, hw1, hnW, hdstW, hdisjN, hnw⟩
      · intro _ mem2 pos2 hpCp
        obtain ⟨_, hcp, hfr⟩ := hpCp
        change (∀ i < L, mem2 (dstPtr + i) = mem (numPtr + i)) at hcp
        change (∀ a, (a < dstPtr ∨ dstPtr + L ≤ a) → mem2 a = mem a) at hfr
        refine WordRAM.runs_ret_le (v := 0) (by simp [Expr.eval, show 0 < 2 ^ w by omega]) ?_ ?_
        · dsimp only [updateCoreLenEdgeContract]
          simp only [Outcome.value, List.getD_cons_zero, List.getD_cons_succ]
          refine ⟨trivial, fun i hi => (hcp i hi) ▸ hvN i hi, ?_, hfr⟩
          have hdstEq : Num.fixVal mem2 dstPtr h L P = Num.fixVal mem numPtr h L P := by
            unfold Num.fixVal; rw [Num.intVal_congr hcp]
          rw [hdstEq]
          have hst := stretch_coreLen_exact hdenPos rfl hcase
          rw [ite_eq_right hneFix] at hst
          exact hst
        · simp only [updateCoreLenEdgeContract, updateCoreLenEdgeCost, Num.equalContract,
            copyLimbsToContract, List.getD_cons_zero, List.getD_cons_succ, Expr.size, argsSize]
          omega

end MinCostFlow.MinRatio
