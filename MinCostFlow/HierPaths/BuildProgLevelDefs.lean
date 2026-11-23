module

public import MinCostFlow.HierPaths.BuildProgGameBudget
public import MinCostFlow.HierPaths.BuildProgChoiceProcs
import MinCostFlow.HierPaths.InitLayout

/-!
# The complete one-parent static level builder

This file assembles the full Word-RAM procedure block `buildLevelProcs` for a single parent group,
combining the singleton fast path (`s = 1`, `buildSingletonProc`) with the non-singleton pipeline
(`1 < s`: core-level computation, game setup, certified batched game loop, final injection, walk
collection, CSR writers for sections 0 and 1, hole-skipping workspace reclamation, sibling
connector packing for section 2, and top-level layout offsets).

The main theorems prove determinism (`buildLevelProcs_noRand`) and the published level contract
(`buildLevelProcs_providesBuildLevel : ProvidesBuildLevel`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-- Setup part of the non-singleton front half: compute layout parameters and `coreLevel`,
and initialize child graph slots.
Args in registers `0..11`: `buildLevelArgs g x start s k M r Δ L L' bh h`.
Leaves layout addresses in registers `12..22` and `q` in `23`. -/
def buildLevelNonSingletonSetup (fCoreLevel fSetup : ℕ) : Stmt :=
  .assign 12 (.bin .mul (.bin .mul (.bin .mul (.const 32) (.reg 7)) (.reg 10)) (.reg 8)) ;;
  .assign 13 (.bin .add (.bin .mul (.const 49) (.reg 9)) (.const 1)) ;;
  .assign 14 (.bin .add (.reg 13) (.const 1)) ;;
  .assign 15 (.bin .add (.const 2) (.bin .mul (.reg 14) (.reg 3))) ;;
  .assign 16 (.bin .mul (.reg 14) (.bin .div (.reg 3) (.const 2))) ;;
  .assign 17 (.bin .add (.reg 11) (.reg 13)) ;;
  .assign 18 (.bin .add (.reg 17) (.reg 4)) ;;
  .assign 19 (.bin .add (.reg 18) (.reg 4)) ;;
  .assign 20 (.bin .add (.reg 19) (.reg 4)) ;;
  .assign 21 (.bin .add (.reg 20) (.bin .mul (.reg 4) (.reg 15))) ;;
  .assign 22 (.bin .add (.bin .add (.reg 21) (.reg 4)) (.const 1)) ;;
  .call 23 fCoreLevel [.reg 5, .reg 6, .reg 3] ;;
  .call 24 fSetup [.reg 18, .reg 19, .reg 20, .reg 2, .reg 3, .reg 4, .reg 15]

/-- Game part of the non-singleton front half: run the certified game loop and final injection.
Leaves `heap1` in register `25` and `injEnd` in register `26`. -/
def buildLevelNonSingletonGame (fGameLoop fInjectEnd : ℕ) : Stmt :=
  .call 25 fGameLoop [.reg 23, .reg 5, .reg 6, .reg 4, .reg 18, .reg 19, .reg 22, .reg 21,
    .reg 3, .reg 0, .reg 1, .reg 7, .reg 8, .reg 12, .bin .mul (.reg 3) (.reg 4),
    .reg 2, .reg 17, .reg 11, .reg 13] ;;
  .call 26 fInjectEnd [.reg 0, .reg 1, .reg 17, .reg 2, .reg 3, .reg 4, .reg 7, .reg 8,
    .reg 25, .reg 18, .reg 19, .reg 20, .reg 15, .reg 21, .reg 12]

/-- Front half of the non-singleton level builder: compute layout parameters and `coreLevel`,
initialize child slots, run the certified game loop, and execute the final injection.
Args in registers `0..11`: `buildLevelArgs g x start s k M r Δ L L' bh h`.
Leaves layout addresses in registers `12..22`, `q` in `23`, `heap1` in `25`, `injEnd` in `26`. -/
def buildLevelNonSingletonFront (fCoreLevel fSetup fGameLoop fInjectEnd : ℕ) : Stmt :=
  buildLevelNonSingletonSetup fCoreLevel fSetup ;;
  buildLevelNonSingletonGame fGameLoop fInjectEnd

/-- First part of the non-singleton back half: collect archived walks, write sections 0, 1,
and 2 consecutively starting at `outStart`. -/
def buildLevelNonSingletonBack1 (fCollectWalks fSec0 fSec1 fConnAll : ℕ) : Stmt :=
  .assign 27 (.bin .add (.reg 26) (.reg 4)) ;;
  .assign 28 (.bin .add (.reg 27) (.bin .mul (.reg 4) (.reg 16))) ;;
  .call 24 fCollectWalks [.reg 11, .reg 13, .reg 2, .reg 3, .reg 4, .reg 25, .reg 26, .reg 27, .reg 16] ;;
  .call 29 fSec0 [.reg 0, .reg 2, .reg 3, .reg 4, .reg 20, .reg 15, .reg 28] ;;
  .call 30 fSec1 [.reg 4, .reg 26, .reg 27, .reg 16, .reg 29] ;;
  .call 31 fConnAll [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 7, .reg 8, .reg 12, .reg 30]

/-- Second part of the non-singleton back half: read `end2` from section 2's CSR header,
copy sections 0, 1, and 2 down to `h + 4`, store the four top-level section offsets at `h..h+3`,
and return the bump heap end `vFinal` from register `31`. -/
def buildLevelNonSingletonBack2 (fCopy : ℕ) : Stmt :=
  .assign 32 (.bin .mul (.reg 4) (.reg 4)) ;;
  .assign 32 (.bin .add (.bin .add (.bin .add (.reg 30) (.reg 32)) (.const 1))
    (.load (.bin .add (.reg 30) (.reg 32)))) ;;
  .call 33 fCopy [.reg 28, .bin .sub (.reg 32) (.reg 28), .bin .add (.reg 11) (.const 4)] ;;
  .store (.reg 11) (.const 0) ;;
  .store (.bin .add (.reg 11) (.const 1)) (.bin .sub (.reg 29) (.reg 28)) ;;
  .store (.bin .add (.reg 11) (.const 2)) (.bin .sub (.reg 30) (.reg 28)) ;;
  .store (.bin .add (.reg 11) (.const 3)) (.bin .sub (.reg 32) (.reg 28)) ;;
  .ret (.reg 31)

/-- Back half of the non-singleton level builder: collect archived walks, write sections 0, 1,
and 2 consecutively, copy them down to `h + 4`, store the four top-level offsets, and return
the bump heap end `end2`. -/
def buildLevelNonSingletonBack (fCollectWalks fSec0 fSec1 fConnAll fCopy : ℕ) :
    Stmt :=
  buildLevelNonSingletonBack1 fCollectWalks fSec0 fSec1 fConnAll ;;
  buildLevelNonSingletonBack2 fCopy

/-- Complete non-singleton (`1 < s`) one-parent level builder procedure. -/
def buildLevelNonSingletonProc (fCoreLevel fSetup fGameLoop fInjectEnd fCollectWalks
    fSec0 fSec1 fConnAll fCopy : ℕ) : Stmt :=
  buildLevelNonSingletonFront fCoreLevel fSetup fGameLoop fInjectEnd ;;
  buildLevelNonSingletonBack fCollectWalks fSec0 fSec1 fConnAll fCopy

/-- Entry procedure for one parent group: dispatches on `s = 1` vs `1 < s`. -/
def buildLevelEntryProc (fSing fNonSing : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 3) (.const 1))
    (.call 12 fSing (List.range 12 |>.map Expr.reg) ;; .ret (.reg 12))
    (.call 12 fNonSing (List.range 12 |>.map Expr.reg) ;; .ret (.reg 12))

/-- The 26 auxiliary procedures placed immediately after `buildGameProcs (b + 1) router core`. -/
def buildLevelTailProcs (b : ℕ) : List Stmt :=
  let g := b + 1
  let t := b + 34
  [ buildCoreLevelProc,
    buildGameSetupProc,
    buildInjectSidesProc (g + 8) (g + 10),
    buildInjectionProc (t + 2),
    buildInjectRouteProc (t + 3) (g + 27),
    buildInjectTablesProc,
    buildInjectFinishProc (t + 5) (g + 15),
    buildInjectEndProc (t + 4) (t + 6),
    buildAppendRowWalksProc,
    buildCollectRoundProc (t + 8),
    buildCollectWalksProc (t + 9) (t + 8),
    buildSec0Proc,
    buildSec1Proc (g + 13),
    buildCollectHolesProc,
    buildReclaimHolesProc (g + 13) (g + 28),
    buildConnRequestProc,
    buildConnRouteProc (t + 15) (g + 27),
    buildConnEraseProc (g + 21),
    buildConnectorRowProc (g + 13),
    initCSRWrite (t + 18),
    buildConnOneProc (t + 16) (t + 17) (t + 19),
    .nop,
    .nop,
    buildConnAllProc (t + 20) (g + 13),
    buildSingletonProc (t + 23),
    buildLevelNonSingletonProc (t + 0) (t + 1) (g + 0) (t + 7)
      (t + 10) (t + 11) (t + 12) (t + 23) (g + 13) ]

/-- Full procedure block for the one-parent level builder, starting at offset `b`.
Index `b` is the entry procedure `buildLevelEntryProc`. -/
def buildLevelProcs (b router core : ℕ) : List Stmt :=
  [buildLevelEntryProc (b + 58) (b + 59)] ++
    buildGameProcs (b + 1) router core ++
    buildLevelTailProcs b

theorem buildLevelNonSingletonProc_noRand (fCoreLevel fSetup fGameLoop fInjectEnd fCollectWalks
    fSec0 fSec1 fConnAll fCopy : ℕ) :
    (buildLevelNonSingletonProc fCoreLevel fSetup fGameLoop fInjectEnd fCollectWalks
      fSec0 fSec1 fConnAll fCopy).NoRand := by
  simp [buildLevelNonSingletonProc, buildLevelNonSingletonFront, buildLevelNonSingletonSetup,
    buildLevelNonSingletonGame, buildLevelNonSingletonBack, buildLevelNonSingletonBack1,
    buildLevelNonSingletonBack2, Stmt.NoRand]

theorem buildLevelEntryProc_noRand (fSing fNonSing : ℕ) :
    (buildLevelEntryProc fSing fNonSing).NoRand := by
  simp [buildLevelEntryProc, Stmt.NoRand]

/-- Every procedure in `buildLevelProcs` is deterministic (`NoRand`). -/
theorem buildLevelProcs_noRand (b router core : ℕ) :
    ∀ stmt ∈ buildLevelProcs b router core, stmt.NoRand := by
  intro stmt hmem
  simp only [buildLevelProcs, buildGameProcs, buildLevelTailProcs,
    List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with ((rfl |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
     rfl | rfl | rfl | rfl | rfl | rfl))
  all_goals first
    | exact buildLevelEntryProc_noRand ..
    | exact buildGameLoopProc_noRand ..
    | exact buildGameStepProc_noRand ..
    | exact buildOneRoundProc_noRand ..
    | exact buildPreparedEndProc_noRand
    | exact buildGameAdvanceProc_noRand ..
    | exact buildGameScanProc_noRand ..
    | exact buildPrepareChildProc_noRand ..
    | exact buildRequestProc_noRand ..
    | exact buildCutMaskProc_noRand
    | exact buildPadHalfProc_noRand
    | exact buildCutPackProc_noRand
    | exact buildRoundRouteProc_noRand ..
    | exact buildGameSelectProc_noRand
    | exact buildCopyProc_noRand
    | exact buildBatchProc_noRand ..
    | exact buildFinishBatchProc_noRand ..
    | exact buildApplyBatchProc_noRand ..
    | exact buildApplyRowProc_noRand ..
    | exact buildMatchReadProc_noRand
    | exact buildGameAppendProc_noRand ..
    | exact buildLocalEndsProc_noRand
    | exact buildWalkRowProc_noRand ..
    | exact buildStoreWalkProc_noRand ..
    | exact pathProc_noRand ..
    | exact buildEraseProc_noRand ..
    | exact buildSaveCoreProc_noRand
    | exact buildActiveCompactProc_noRand
    | exact buildFullRouteProc_noRand ..
    | exact zeroProc_noRand
    | exact vertsProc_noRand
    | exact posFillProc_noRand
    | exact jumpProc_noRand
    | exact posClearProc_noRand
    | exact buildCoreLevelProc_noRand
    | exact buildGameSetupProc_noRand
    | exact buildInjectSidesProc_noRand ..
    | exact buildInjectionProc_noRand ..
    | exact buildInjectRouteProc_noRand ..
    | exact buildInjectTablesProc_noRand
    | exact buildInjectFinishProc_noRand ..
    | exact buildInjectEndProc_noRand ..
    | exact buildAppendRowWalksProc_noRand
    | exact buildCollectRoundProc_noRand ..
    | exact buildCollectWalksProc_noRand ..
    | exact buildSec0Proc_noRand
    | exact buildSec1Proc_noRand ..
    | exact buildCollectHolesProc_noRand
    | exact buildReclaimHolesProc_noRand ..
    | exact buildConnRequestProc_noRand
    | exact buildConnRouteProc_noRand ..
    | exact buildConnEraseProc_noRand ..
    | exact buildConnectorRowProc_noRand ..
    | exact initCSRWrite_noRand ..
    | exact buildConnOneProc_noRand ..
    | exact buildConnAllProc_noRand ..
    | exact buildSingletonProc_noRand ..
    | exact buildLevelNonSingletonProc_noRand ..
    | simp [buildEraseProc, pathProc, vertsProc, vertsBody, jumpProc, jumpBody, forRange, forUp, Stmt.NoRand]

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp MinCostFlow.Spanner

/-! ### Lookup helpers for `buildLevelProcs` -/

theorem buildLevelProcs_gameSplit {p : Program} {prior later : List Stmt}
    {router core : ℕ}
    (hp : p.procs = prior ++ buildLevelProcs prior.length router core ++ later) :
    let prior' := prior ++ [buildLevelEntryProc (prior.length + 58) (prior.length + 59)]
    p.procs = prior' ++ buildGameProcs prior'.length router core ++
      (buildLevelTailProcs prior.length ++ later) := by
  intro prior'
  have hlen : prior'.length = prior.length + 1 := by simp [prior']
  rw [hlen, hp]
  simp only [buildLevelProcs, prior', List.append_assoc]

theorem buildLevelProcs_lookup_entry {p : Program} {prior later : List Stmt}
    {router core : ℕ}
    (hp : p.procs = prior ++ buildLevelProcs prior.length router core ++ later) :
    p.procs[prior.length]? = some (buildLevelEntryProc (prior.length + 58) (prior.length + 59)) := by
  rw [hp, List.append_assoc, List.getElem?_append_right le_rfl, Nat.sub_self]
  simp [buildLevelProcs]

theorem buildLevelProcs_lookup_game {p : Program} {prior later : List Stmt}
    {router core : ℕ}
    (hp : p.procs = prior ++ buildLevelProcs prior.length router core ++ later)
    (i : ℕ) (hi : i < 33) :
    p.procs[prior.length + 1 + i]? = (buildGameProcs (prior.length + 1) router core)[i]? := by
  have hsp := buildLevelProcs_gameSplit hp
  have hlen : (prior ++ [buildLevelEntryProc (prior.length + 58) (prior.length + 59)]).length =
      prior.length + 1 := by simp
  simpa [hlen] using buildGameProcs_lookup hsp i hi

theorem buildLevelProcs_lookup_tail {p : Program} {prior later : List Stmt}
    {router core : ℕ}
    (hp : p.procs = prior ++ buildLevelProcs prior.length router core ++ later)
    (i : ℕ) (hi : i < 26) :
    p.procs[prior.length + 34 + i]? = (buildLevelTailProcs prior.length)[i]? := by
  have hgameLen : (buildGameProcs (prior.length + 1) router core).length = 33 := by
    simp [buildGameProcs]
  have htailLen : (buildLevelTailProcs prior.length).length = 26 := by
    simp [buildLevelTailProcs]
  have hpref : (prior ++ [buildLevelEntryProc (prior.length + 58) (prior.length + 59)] ++
      buildGameProcs (prior.length + 1) router core).length = prior.length + 34 := by
    simp [hgameLen]
  rw [hp]
  have hrw : prior ++ buildLevelProcs prior.length router core ++ later =
      (prior ++ [buildLevelEntryProc (prior.length + 58) (prior.length + 59)] ++
        buildGameProcs (prior.length + 1) router core) ++
      (buildLevelTailProcs prior.length ++ later) := by
    simp only [buildLevelProcs, List.append_assoc]
  rw [hrw, List.getElem?_append_right (by omega), hpref, Nat.add_sub_cancel_left,
    List.getElem?_append_left (by omega)]

/-! ### Assembled subprocedure contracts from `buildLevelProcs` -/

theorem buildLevelProcs_connAll_meetsContract {w K C router core : ℕ}
    {route : RouterFn} {routeCost : RouterCostFn} {sR : ℕ → ℕ → ℕ → ℕ → ℕ}
    {G : Graph} {start s k Δ L bh : ℕ} {β : ℝ} {p : Program} {prior later : List Stmt}
    (hp : p.procs = prior ++ buildLevelProcs prior.length router core ++ later)
    (hRouter : ProvidesRouter w K route routeCost sR p router)
    (hPlayer : IsMatchingPlayer route routeCost)
    (hC : RouteCostLe routeCost C)
    (hValid : G.IsValid) (hPos : 0 < β)
    (hExp : G.IsExpansionExpanderOn (buildLevelVerts start s k) β)
    (hBh : max 2 (2 / β) ≤ (bh : ℝ))
    (hCardW : (buildLevelVerts start s k).card < 2 ^ w) :
    MeetsContract w p (prior.length + 57)
      (buildConnAllContract w K C route sR G start s k Δ L bh) := by
  let b := prior.length
  let g := b + 1
  have hg (i : ℕ) (hi : i < 33) := buildLevelProcs_lookup_game hp i hi
  have ht (i : ℕ) (hi : i < 26) := buildLevelProcs_lookup_tail hp i hi
  have hg13 := hg 13 (by decide)
  have hg21 := hg 21 (by decide)
  have hg22 := hg 22 (by decide)
  have hg23 := hg 23 (by decide)
  have hg24 := hg 24 (by decide)
  have hg27 := hg 27 (by decide)
  have hg29 := hg 29 (by decide)
  have hg30 := hg 30 (by decide)
  have hg31 := hg 31 (by decide)
  have hg32 := hg 32 (by decide)
  have ht15 := ht 15 (by decide)
  have ht16 := ht 16 (by decide)
  have ht17 := ht 17 (by decide)
  have ht18 := ht 18 (by decide)
  have ht19 := ht 19 (by decide)
  have ht20 := ht 20 (by decide)
  have ht23 := ht 23 (by decide)
  simp only [buildGameProcs, List.getElem?_cons_succ, List.getElem?_cons_zero] at hg13 hg21 hg22 hg23 hg24 hg27 hg29 hg30 hg31 hg32
  simp only [buildLevelTailProcs, List.getElem?_cons_succ, List.getElem?_cons_zero] at ht15 ht16 ht17 ht18 ht19 ht20 ht23
  refine buildConnAllProc_meetsContract (fPair := b + 54) (fCopy := g + 13)
    (by simpa [b, g] using ht23) (by simpa [b, g] using hg13)
    hPlayer (fun pairs b' hRPre hb' => hC G (buildLevelVerts start s k) pairs Δ L b' 0
      hRPre.1 hRPre.2.1 hRPre.2.2.1 hRPre.2.2.2.1 hRPre.2.2.2.2.1 hRPre.2.2.2.2.2.1 hb'
      hRPre.2.2.2.2.2.2) ?_
  intro a bb M emb hRes hMlen args mem pos ω hWords hPre
  have hPreCopy := hPre
  obtain ⟨_, _, _, _, hRPre, _, _, _⟩ := hPreCopy
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hRouterPre⟩ := hRPre
  obtain ⟨_, hex⟩ := exists_lemma_1 hPlayer
  obtain ⟨⟨Ms', emb', hRes', hMatch', _⟩, _, hLast, _, _⟩ :=
    hex G (buildLevelVerts start s k) (connRequestPairs a bb M.length) Δ L
      hRouterPre (by simp [connRequestPairs]) β hPos hExp
  have hResEq : (lemma1Route route G (buildLevelVerts start s k)
      (connRequestPairs a bb M.length) Δ L).1 = .matched [M] emb := by
    rwa [hMlen]
  rw [hResEq] at hRes'
  cases hRes'
  have hDenomLe : (lemma1Route route G (buildLevelVerts start s k)
      (connRequestPairs a bb M.length) Δ L).2 ≤ bh := by
    have hR : ((lemma1Route route G (buildLevelVerts start s k)
        (connRequestPairs a bb M.length) Δ L).2 : ℝ) ≤ (bh : ℝ) := hLast.trans hBh
    exact_mod_cast hR
  have hPath : routePathLen Δ (lemma1Route route G (buildLevelVerts start s k)
      (connRequestPairs a bb M.length) Δ L).2 L ≤ routePathLen Δ bh L := by
    unfold routePathLen; gcongr
  have hPair : MeetsContract w p (b + 54)
      (buildConnOneContract w K route routeCost sR G (buildLevelVerts start s k) a bb Δ L
        (routePathLen Δ bh L) M emb) := by
    refine buildConnOneProc_meetsContract (fRoute := b + 50) (fErase := b + 51) (fGather := b + 53)
      (denom := (lemma1Route route G (buildLevelVerts start s k)
        (connRequestPairs a bb M.length) Δ L).2)
      (by simpa [b] using ht20) ?_ ?_ ?_ hValid hMatch' hResEq hPath
    · exact buildConnRouteProc_meetsContract (fRequest := b + 49) (fFull := g + 27)
        (fRouter := router) (fCopy := g + 13)
        (by simpa [b, g] using ht16) (by simpa [b] using ht15)
        (by simpa [b, g] using hg27) hRouter (by simpa [b, g] using hg13)
        hPlayer hExp hPos hCardW
    · refine buildConnEraseProc_meetsContract (fWalk := g + 21) (by simpa [b, g] using ht17) ?_
      refine buildWalkRowProc_meetsContract (by simpa [b, g] using hg21) fun j _ => ?_
      exact buildStoreWalkProc_meetsContract (by simpa [b, g] using hg22)
        (pathProc_meetsContract (by simpa [b, g] using hg23) (by simpa [b, g] using hg29)
          (by simpa [b, g] using hg24) (by simpa [b, g] using hg30)
          (by simpa [b, g] using hg31) (by simpa [b, g] using hg32))
    · intro ctx n
      exact buildConnectorGather_meetsContract (fRow := b + 52) (fCopy := g + 13)
        (by simpa [b] using ht19) (by simpa [b, g] using ht18) (by simpa [b, g] using hg13)
  exact hPair args mem pos ω hWords hPre

theorem buildLevelProcs_injectEnd_meetsContract {w router core heap slot runEnd : ℕ}
    {p : Program} {prior later : List Stmt} {D : ChoiceLoopData} {β : ℝ} {bh : ℕ}
    {initial last : ℕ → ℕ} {sts : ℕ → ChildState}
    {Ms : List (List (ℕ × ℕ))} {emb : ℕ → List ℕ}
    (hp : p.procs = prior ++ buildLevelProcs prior.length router core ++ later)
    (hRouter : ProvidesRouter w D.base.K D.base.route D.base.routeCost D.base.routeSpace p router)
    (hTrace : ChoiceLoopTrace w D initial D.limit heap sts last)
    (h : ChoiceGameHyp D β bh) (hL : GameFixedLayout w D.geometry)
    (hCardW : D.base.verts.card < 2 ^ w)
    (hRes : lemma1Route D.base.route D.base.host D.base.verts
      (injPairs D.base.childSize D.count D.offset sts) D.base.Δ D.base.L = (.matched Ms emb, runEnd))
    (hB : runEnd ≤ bh)
    (hMatch : RouteMatchedSpec D.base.host D.base.verts
      (injPairs D.base.childSize D.count D.offset sts) D.base.Δ D.base.L runEnd 0 Ms emb)
    (hFull : ∀ i (hi : i < (injPairs D.base.childSize D.count D.offset sts).length),
      (Ms.getD i []).length = ((injPairs D.base.childSize D.count D.offset sts)[i]'hi).1.card) :
    MeetsContract w p (prior.length + 41) (buildInjectEndContract w D heap slot sts Ms emb) := by
  let b := prior.length
  let g := b + 1
  have hg (i : ℕ) (hi : i < 33) := buildLevelProcs_lookup_game hp i hi
  have ht (i : ℕ) (hi : i < 26) := buildLevelProcs_lookup_tail hp i hi
  have hg8 := hg 8 (by decide)
  have hg10 := hg 10 (by decide)
  have hg13 := hg 13 (by decide)
  have hg15 := hg 15 (by decide)
  have hg16 := hg 16 (by decide)
  have hg17 := hg 17 (by decide)
  have hg18 := hg 18 (by decide)
  have hg19 := hg 19 (by decide)
  have hg20 := hg 20 (by decide)
  have hg21 := hg 21 (by decide)
  have hg22 := hg 22 (by decide)
  have hg23 := hg 23 (by decide)
  have hg24 := hg 24 (by decide)
  have hg27 := hg 27 (by decide)
  have hg29 := hg 29 (by decide)
  have hg30 := hg 30 (by decide)
  have hg31 := hg 31 (by decide)
  have hg32 := hg 32 (by decide)
  have ht2 := ht 2 (by decide)
  have ht3 := ht 3 (by decide)
  have ht4 := ht 4 (by decide)
  have ht5 := ht 5 (by decide)
  have ht6 := ht 6 (by decide)
  have ht7 := ht 7 (by decide)
  simp only [buildGameProcs, List.getElem?_cons_succ, List.getElem?_cons_zero] at hg8 hg10 hg13 hg15 hg16 hg17 hg18 hg19 hg20 hg21 hg22 hg23 hg24 hg27 hg29 hg30 hg31 hg32
  simp only [buildLevelTailProcs, List.getElem?_cons_succ, List.getElem?_cons_zero] at ht2 ht3 ht4 ht5 ht6 ht7
  refine buildInjectEndProc_meetsContract (fRoute := b + 38) (fFinish := b + 40)
    hTrace h hL (by simpa [b] using ht7) ?_ ?_ hRes hB hMatch hFull
  · exact buildInjectRouteProc_meetsContract (fBatch := b + 37) (fSides := b + 36)
      (fMask := g + 8) (fPack := g + 10) (fFull := g + 27) (fRoute := router) (fCopy := g + 13)
      (by simpa [b, g] using ht4) (by simpa [b] using ht3) (by simpa [b, g] using ht2)
      (by simpa [b, g] using hg8) (by simpa [b, g] using hg10)
      (by simpa [b, g] using hg27) hRouter (by simpa [b, g] using hg13)
      h.router h.positive h.expansion hCardW
  · refine buildInjectFinishProc_meetsContract (fTables := b + 39) (fFinish := g + 15)
      (by simpa [b, g] using ht6) (by simpa [b] using ht5) ?_
    apply buildFinishBatchProc_meetsContract (by simpa [b, g] using hg15)
    refine buildApplyBatchProc_meetsContract (by simpa [b, g] using hg16) fun i _ => ?_
    refine buildApplyRowProc_meetsContract (by simpa [b, g] using hg17)
      (by simpa [b, g] using hg18) (by simpa [b, g] using hg19)
      (by simpa [b, g] using hg20) (by simpa [b, g] using hg21) fun j _ => ?_
    exact buildStoreWalkProc_meetsContract (by simpa [b, g] using hg22)
      (pathProc_meetsContract (by simpa [b, g] using hg23) (by simpa [b, g] using hg29)
        (by simpa [b, g] using hg24) (by simpa [b, g] using hg30)
        (by simpa [b, g] using hg31) (by simpa [b, g] using hg32))


end MinCostFlow.HierPaths
