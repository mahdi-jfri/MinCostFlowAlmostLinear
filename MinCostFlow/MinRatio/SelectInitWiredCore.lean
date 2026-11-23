module

public import MinCostFlow.MinRatio.SelectInitBody
public import MinCostFlow.MinRatio.SolverInitWired
public import MinCostFlow.MinRatio.OrdSolverImplementsFull
import WordRAM.Tactic

/-!
# Core helpers for wired solver initialization with select region (`SelectInitWiredCore`)

Defines the fixed deterministic Word-RAM initializer `solverInitWiredSelBody` (composing
`solverInitWiredBody`, `G_d` extraction via `op 3` + `dgInitEmpty` + `dgCopyRefill`, and
`selectInitRegionBody` with runtime `cap = 2 * eCap`), its space/cost bounds, and the two core
sub-lemmas:
* `init_meta_hyps_of_caps`: derives all select-region metadata footprint bounds from
  `solverStateRepFull.rep` and `SolverLevelCapsInv`.
* `op3_copy_gd_runs`: executes the `d > 0` branch (`op 3` on core `d - 1`, `dgInitEmpty`, and
  `dgCopyRefill`), producing a copy of `G_d` disjoint from every `Rcore.foot` and from the
  select-handle cells while preserving `solverStateRepFull.rep` and `SolverLevelCapsInv`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program
open MinCostFlow.LastLevelProgram

/-- Read-only contract for computing the terminal stretch precision `pLast` from `[m]`. -/
def selectPLastContract (w m pLast pLastCost : ℕ) : Contract where
  pre args _ := args = [m] ∧ pLast < 2 ^ w
  post _ mem ret mem' := mem' = mem ∧ ret = pLast
  cost _ _ := pLastCost

/-- Read-only contract for computing the embedding slot size `slot` from `[m, V, L, P]`. -/
def selectSlotContract (w m V L P slot slotCost : ℕ) : Contract where
  pre args _ := args = [m, V, L, P] ∧ slot < 2 ^ w
  post _ mem ret mem' := mem' = mem ∧ ret = slot
  cost _ _ := slotCost

/-- Fixed deterministic solver initializer with select region.
Arguments (`reg 0..6`): `[graph, gradient, lengths, L, P, V, root]`.
Calls `wiredInitProc` (`solverInitWiredBody`), computes `cap = 2 * eCap`, extracts `srcGd`
(`op3Proc` + `dgEmptyProc` + `dgCopyProc` when `d > 0`, or `rootGraph` when `d = 0`), and calls
`selInitProc` (`selectInitRegionBody`), returning the final heap pointer. -/
def solverInitWiredSelBody
    (wiredInitProc op3Proc dgEmptyProc dgCopyProc selInitProc pLastProc slotProc : ℕ) : Stmt :=
  .call 7 wiredInitProc [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4, .reg 5, .reg 6] ;;
  .assign 8 (.load (.reg 6)) ;; -- handle
  .assign 9 (.load (.bin .add (.reg 6) (.const 1))) ;; -- table
  .assign 10 (.load (.bin .add (.reg 6) (.const 14))) ;; -- rootGraph
  .assign 11 (.load (.bin .add (.reg 8) (.const 9))) ;; -- m
  .assign 12 (.load (.bin .add (.reg 8) (.const 11))) ;; -- d
  .assign 13 (.load (.reg 10)) ;; -- vCap = G.n
  .assign 14 (.load (.bin .add (.reg 10) (.const 1))) ;; -- eCap = initTargetCap
  .assign 15 (.bin .mul (.const 2) (.reg 14)) ;; -- cap = selectHeapCap = 2 * eCap
  .assign 16 (.bin .add (.reg 8) (.const 18)) ;; -- levelTable
  .assign 17 (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 2) (.reg 12))) (.const 2)) ;; -- lvlMeta
  .assign 18 (.bin .add (.bin .add (.reg 9) (.bin .mul (.const 4) (.reg 12))) (.const 2)) ;; -- hbCell
  .call 19 pLastProc [.reg 11] ;; -- pLast
  .call 20 slotProc [.reg 11, .reg 5, .reg 3, .reg 4] ;; -- slot
  .cond (.reg 12)
    (.assign 21 (.load (.bin .add (.reg 16) (.bin .sub (.reg 12) (.const 1)))) ;; -- coreHandle (d-1)
     .assign 22 (.load (.bin .add (.bin .add (.reg 16) (.bin .add (.reg 12) (.const 1)))
       (.bin .sub (.reg 12) (.const 1)))) ;; -- bran (d-1)
     .call 23 op3Proc [.reg 21, .reg 22, .reg 7] ;; -- cur1
     .assign 24 (.load (.reg 7)) ;; -- gPtr
     .call 25 dgEmptyProc [.reg 23, .reg 13, .reg 14] ;;
     .assign 26 (.bin .add (.bin .add (.bin .add (.reg 23) (.const 4)) (.bin .mul (.const 7) (.reg 13)))
       (.bin .mul (.const 9) (.reg 14))) ;; -- cur1 + dynGraphSize vCap eCap
     .call 27 dgCopyProc [.reg 23, .reg 24, .reg 26] ;; -- cur2
     .assign 28 (.reg 23) ;; -- srcGd = cur1
     .assign 29 (.reg 27)) -- sb = cur2
    (.assign 28 (.reg 10) ;; -- srcGd = rootGraph
     .assign 29 (.reg 7)) ;; -- sb = cur0
  .call 30 selInitProc
    [.reg 29, .reg 15, .reg 12, .reg 13, .reg 14, .reg 3, .reg 20, .reg 16, .reg 17,
     .reg 19, .reg 18, .reg 1, .reg 28, .reg 2] ;;
  .ret (.reg 30)

theorem solverInitWiredSelBody_noRand (a b c d e f g : ℕ) :
    (solverInitWiredSelBody a b c d e f g).NoRand := by
  simp [solverInitWiredSelBody, Stmt.NoRand]

/-- Total select-region heap space used above `finalHeap` of `solverInitWiredBody`. -/
noncomputable def solverInitWiredSelSpace {T : SparseCoreRestartTool} {P : ChainParams}
    (C : ChainState T P) (vCap eCap cap L capExp slot op3Space evalSpace : ℕ) : ℕ :=
  op3Space + dynGraphSize vCap eCap + 3 * (C.G P.d).m +
  selectHeapSize cap P.d L + selectLevelMetaSize P.d +
  (⟨0, P.d, vCap, eCap, L, slot⟩ : SelectBlocksLoc).endAddr +
  selectInitRegionScratch C cap L capExp evalSpace

/-- Total step cost overhead of the select-region initialization tail above `solverInitWiredBody`. -/
noncomputable def solverInitWiredSelCost {T : SparseCoreRestartTool} {P : ChainParams}
    (C : ChainState T P) (readoutCost cap L capExp slot evalCost pLastCost slotCost : ℕ) : ℕ :=
  pLastCost + slotCost +
  readoutCost + 40 + dgCopyRefillCost 0 0 (C.G P.d).n (C.G P.d).m +
  selectInitRegionCost C readoutCost cap L capExp slot evalCost + 320

end MinCostFlow.MinRatio

end

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain IPM.Machine Num DynSpanner.Program SparseCore.Program
open MinCostFlow.LastLevelProgram

theorem selectHeapCap_eq_two_mul_initTargetCap (cfg : Alg2Config) (G : MGraph) (m : ℕ)
    (hm : G.m = m) :
    selectHeapCap cfg G m = 2 * initTargetCap cfg G := by
  unfold selectHeapCap initTargetCap; rw [hm]

theorem solverLevelMetaAddr_eq (table d : ℕ) :
    solverLevelMetaAddr table d = table + 2 * d + 2 := by
  unfold solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega

theorem solverSelectHeapAddr_eq (table d : ℕ) :
    solverSelectHeapAddr table d = table + 4 * d + 2 := by
  unfold solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega

theorem solverSelectBlocksAddr_eq (table d : ℕ) :
    solverSelectBlocksAddr table d = table + 4 * d + 3 := by
  unfold solverSelectBlocksAddr solverSelectHeapAddr solverLevelMetaAddr solverLvlMAddr solverN0Addr; omega

theorem blocks_endAddr_eq_base_add (base d vCap eCap L slot : ℕ) :
    (⟨base, d, vCap, eCap, L, slot⟩ : SelectBlocksLoc).endAddr =
      base + (⟨0, d, vCap, eCap, L, slot⟩ : SelectBlocksLoc).endAddr := by
  simp only [SelectBlocksLoc.endAddr_eq]; omega

/-- Derives the select-init metadata bounds (`hhbMeta`, `hhbTagOff`, `hhbBelow`, `hhbDisjMeta`,
`hMetaBelow`) from `solverStateRepFull.rep`, `SolverLevelCapsInv`, and footprint `< sb`. -/
theorem init_meta_hyps_of_caps
    {L P m V psi k epsExp drainUnit unit toolMul treeMul vCap eCap sb root : ℕ}
    {cfg : Alg2Config} {κ : ℝ} {G : MGraph} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {model : Alg2State cfg}
    {tokFull : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).τ}
    {mem : ℕ → ℕ}
    (hrepFull : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
      Rcore).rep root model tokFull mem)
    (hFootBelow : ∀ a, (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul
      treeMul Rcore).foot root tokFull a → a < sb)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tokFull.1.1 mem) :
    let tok := tokFull.1.1
    LevelMetaFoot tok (tok.table + 4 * cfg.P.d + 2) ∧
    (∀ a, a = tok.table + 4 * cfg.P.d + 2 ∨ a = tok.table + 4 * cfg.P.d + 3 →
      (∀ v, 1 ≤ v → v ≤ 20 + cfg.P.d → tok.tag a ≠ v) ∧
      tok.tag a ≠ 22 + cfg.P.d ∧ tok.tag a ≠ 23 + cfg.P.d) ∧
    tok.table + 4 * cfg.P.d + 3 < sb ∧
    (tok.table + 4 * cfg.P.d + 3 < solverN0Addr tok.table cfg.P.d ∨
      solverLevelMetaAddr tok.table cfg.P.d + 2 * cfg.P.d ≤ tok.table + 4 * cfg.P.d + 2) ∧
    (tok.handle + 18 + 2 * (cfg.P.d + 1) ≤ sb ∧
      solverLevelMetaAddr tok.table cfg.P.d + 2 * cfg.P.d + 1 ≤ sb ∧
      ∀ j < cfg.P.d,
        mem (solverLevelMetaAddr tok.table cfg.P.d + j) + eCap * L ≤ sb ∧
        solverLevelG tok mem j + dynGraphSize vCap eCap ≤ sb) := by
  intro tok
  dsimp only [tok]
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, htags0⟩ := hrepFull.1.1
  obtain ⟨hOwn0, _, _, _, hTagLvlTbl, _⟩ := htags0
  have hTagLtSb : ∀ a, tokFull.1.1.tag a ≠ 0 → a < sb := fun a hne => hFootBelow a (Or.inl (hOwn0 a hne))
  have htagHb : tokFull.1.1.tag (tokFull.1.1.table + 4 * cfg.P.d + 2) = 21 + cfg.P.d := by
    rw [← solverSelectHeapAddr_eq]; exact hcaps.1.1.2.2.1
  have htagBlk : tokFull.1.1.tag (tokFull.1.1.table + 4 * cfg.P.d + 3) = 21 + cfg.P.d := by
    rw [← solverSelectBlocksAddr_eq]; exact hcaps.1.1.2.2.2
  have hhbLt : tokFull.1.1.table + 4 * cfg.P.d + 3 < sb := hTagLtSb _ (by omega)
  have hHndBelow : tokFull.1.1.handle + 18 + 2 * (cfg.P.d + 1) ≤ sb := by
    have htagLast := hTagLvlTbl (2 * (cfg.P.d + 1) - 1) (by omega)
    have hlt := hTagLtSb (tokFull.1.1.handle + 18 + (2 * (cfg.P.d + 1) - 1)) (by omega)
    omega
  refine ⟨Or.inr (Or.inl htagHb), ?_, hhbLt,
    Or.inr (by rw [solverLevelMetaAddr_eq]; omega), hHndBelow,
    by rw [solverLevelMetaAddr_eq]; omega, fun j hj => ?_⟩
  · intro a ha
    have hta : tokFull.1.1.tag a = 21 + cfg.P.d := by rcases ha with rfl | rfl <;> assumption
    exact ⟨fun v _ _ => by omega, by omega, by omega⟩
  · have hMC := (solverLevelCapsInv_iff_metaCaps.mp hcaps).2.2.2.2.2 j hj
    refine ⟨?_, ?_⟩
    · by_cases heL : eCap * L = 0
      · have := hFootBelow _ (Or.inl hMC.2.2.1); omega
      · have hlt := hTagLtSb (mem (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + j) + eCap * L - 1)
          (by have := hMC.2.2.2.1 (mem (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + j) + eCap * L - 1)
                (by omega) (by omega); omega)
        omega
    · have hDgPos : 0 < dynGraphSize vCap eCap := by unfold dynGraphSize; omega
      have hGeq : solverLevelG tokFull.1.1 mem j =
          mem (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + cfg.P.d + j) := rfl
      have hlt := hTagLtSb (solverLevelG tokFull.1.1 mem j + dynGraphSize vCap eCap - 1)
        (by rw [hGeq]
            have htg := hMC.2.2.2.2
              (mem (solverLevelMetaAddr tokFull.1.1.table cfg.P.d + cfg.P.d + j) +
                dynGraphSize vCap eCap - 1)
              (by omega) (by omega)
            split_ifs at htg <;> omega)
      omega

/-- Executes the `d > 0` branch (`op 3` on core `d - 1`, `dgInitEmpty`, `dgCopyRefill`),
producing a copy of `G_d` at `[cur1, cur1 + dynGraphSize vCap eCap)` disjoint from every
`Rcore.foot` and from `hbCell`/`hbCell + 1`, while preserving `Rfull.rep` and
`SolverLevelCapsInv`. -/
theorem op3_copy_gd_runs
    {w L P m V psi k epsExp drainUnit unit toolMul treeMul depth capExp vCap eCap cur0 op3Space pos : ℕ}
    {dgEmptyProc dgCopyProc : ℕ}
    {fmt : Num.Format w} {cfg : Alg2Config} {κ : ℝ} {G G₀ initialGraph : MGraph}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {Psc : SparseCoreOrdParams} {allocation : ℕ → List ℕ → ℕ}
    {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {op : ℕ → ℕ} {ω : ℕ → Bool}
    {root : ℕ} {model : Alg2State cfg}
    {tokFull : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore).τ}
    {mem : ℕ → ℕ}
    (hlocalCore : Rcore.Local) (hw16 : 16 < 2 ^ w) (hkW : cfg.P.k < 2 ^ w)
    (hdPos : 0 < cfg.P.d)
    (hrepFull : (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul
      Rcore).rep root model tokFull mem)
    (hFootBelow : ∀ a, (solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul
      treeMul Rcore).foot root tokFull a → a < cur0)
    (hcaps : SolverLevelCapsInv P V vCap eCap model tokFull.1.1 mem)
    (hmod : SelectModelInv model G₀ σ σ_mwu γ_ℓ γ_c)
    (hScIn : SparseCoreOrdInput cfg.T cfg.P.k (model.chain.lvlM (cfg.P.d - 1)) model.chain.N₀
      (model.chain.scState (cfg.P.d - 1)) (model.chain.G (cfg.P.d - 1))
      (model.chain.levelOrd (cfg.P.d - 1)) (model.chain.updCount (cfg.P.d - 1)))
    (hBrLt : model.chain.bran (cfg.P.d - 1) < cfg.P.k)
    (hVcapD : ∀ v ∈ (model.chain.G cfg.P.d).V, v < vCap)
    (hEcapD : ∀ e ∈ (model.chain.G cfg.P.d).E, e < eCap)
    (hFootAt : SparseCoreReadoutFootAt fmt L depth cfg.T initialGraph cfg.P.k
      (model.chain.lvlM (cfg.P.d - 1)) model.chain.N₀ vCap eCap capExp Psc allocation Rcore p op)
    (hOp3Sp : 1 ≤ op3Space)
    (hDgEmpty : MeetsContract w p dgEmptyProc (dgInitEmptyContract w))
    (hDgCopy : MeetsContract w p dgCopyProc (dgCopyRefillContract w vCap eCap vCap eCap dgEmptyGraph (model.chain.G cfg.P.d)))
    (hz : ZeroFrom mem cur0)
    (hroom : cur0 + op3Space + dynGraphSize vCap eCap + 3 * (model.chain.G cfg.P.d).m < 2 ^ w) :
    let Rfull := solverStateRepFull cfg κ G L P m V psi k epsExp drainUnit unit toolMul treeMul Rcore
    let j := cfg.P.d - 1
    ∃ b3 o3 st1 c3 bE oE st2 cE bC oC st3 cC tokFull1,
      p.procs[op 3]? = some b3 ∧
      Runs w p ω b3 (startState [tokFull.1.1.coreHandle j, model.chain.bran j, cur0] mem pos) o3 st1 c3 ∧
      p.procs[dgEmptyProc]? = some bE ∧
      Runs w p ω bE (startState [o3.value, vCap, eCap] st1.mem st1.pos) oE st2 cE ∧
      p.procs[dgCopyProc]? = some bC ∧
      Runs w p ω bC (startState [o3.value, st1.mem cur0, o3.value + dynGraphSize vCap eCap] st2.mem st2.pos) oC st3 cC ∧
      cur0 ≤ o3.value ∧ o3.value ≤ cur0 + op3Space ∧
      oC.value = o3.value + dynGraphSize vCap eCap + 3 * (model.chain.G cfg.P.d).m ∧
      Rfull.rep root model tokFull1 st3.mem ∧
      tokFull1.1.1.table = tokFull.1.1.table ∧
      tokFull1.1.1.handle = tokFull.1.1.handle ∧
      tokFull1.1.1.termHandle = tokFull.1.1.termHandle ∧
      tokFull1.1.1.termTok = tokFull.1.1.termTok ∧
      tokFull1.1.1.vcLast = tokFull.1.1.vcLast ∧
      tokFull1.1.1.ecLast = tokFull.1.1.ecLast ∧
      tokFull1.1.1.tree = tokFull.1.1.tree ∧ tokFull1.1.1.trees = tokFull.1.1.trees ∧
      tokFull1.1.1.edgeRecords = tokFull.1.1.edgeRecords ∧
      SolverLevelCapsInv P V vCap eCap model tokFull1.1.1 st3.mem ∧
      DynGraphAt st3.mem o3.value vCap eCap (model.chain.G cfg.P.d) ∧
      (∀ a < cur0, ¬ Rcore.foot (tokFull.1.1.coreHandle j) (tokFull.1.1.coreTok j) a → st3.mem a = mem a) ∧
      (∀ a, Rfull.foot root tokFull1 a → Rfull.foot root tokFull a ∨ (cur0 ≤ a ∧ a < o3.value)) ∧
      ZeroFrom st3.mem oC.value ∧
      c3 + cE + cC + Rfull.phi root tokFull1 st3.mem ≤
        Psc.readout + 40 + dgCopyRefillCost 0 0 (model.chain.G cfg.P.d).n (model.chain.G cfg.P.d).m +
          Rfull.phi root tokFull mem := by
  intro Rfull j
  have hjLt : j < cfg.P.d := by dsimp only [j]; omega
  have hjSucc : j + 1 = cfg.P.d := by dsimp only [j]; omega
  have hGdEq : cfg.T.S (model.chain.scState j) (model.chain.bran j) = model.chain.G cfg.P.d := by
    obtain ⟨_, _, _, hGeq⟩ := hmod.1.2.2.2.2.1 j hjLt
    change model.chain.G (j + 1) = cfg.T.S (model.chain.scState j) (model.chain.bran j) at hGeq
    rw [hjSucc] at hGeq; exact hGeq.symm
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hCores0, _, _, _, _, htags0⟩ := hrepFull.1.1
  obtain ⟨hOwn0, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, hCoreTags⟩ := htags0
  have hCoreRep0 := (hCores0 j hjLt).2.2
  have hHndLt : tokFull.1.1.coreHandle j < cur0 := hFootBelow _ (Or.inl (hcaps.1.2.1 j hjLt))
  have hBrLtJ : model.chain.bran j < cfg.P.k := hBrLt
  have hCoreFootLt : ∀ a, Rcore.foot (tokFull.1.1.coreHandle j) (tokFull.1.1.coreTok j) a → a < cur0 :=
    fun a ha => hFootBelow a (Or.inr (Or.inr ⟨j, hjLt, ha⟩))
  obtain ⟨b3, hb3, o3, st1, c3, y1, hr3, hrep1Core, hpost3, hresp3, hcost3⟩ :=
    hFootAt.op3_runs (tokFull.1.1.coreHandle j) (chainLevelOrdAbs model.chain j)
      (tokFull.1.1.coreTok j) [tokFull.1.1.coreHandle j, model.chain.bran j, cur0] mem pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl) <;> omega)
      rfl hCoreRep0 ⟨hScIn, tokFull.1.1.coreHandle j, model.chain.bran j, cur0, rfl, hBrLtJ⟩
      hCoreFootLt hz (by
        change cur0 + 1 < 2 ^ w
        omega)
  obtain ⟨gVC, gEC, hDG1Raw, hvcEq, hecEq, hGPtrEnd1, _⟩ := hpost3
  rw [hvcEq, hecEq] at hDG1Raw hGPtrEnd1
  have hDG1 : DynGraphAt st1.mem (st1.mem cur0) vCap eCap (model.chain.G cfg.P.d) := hGdEq ▸ hDG1Raw
  obtain ⟨hcur1Lo, hcur1Hi, hz1, hFr1Out, hFoot1⟩ := hresp3
  change cur0 ≤ o3.value at hcur1Lo
  change o3.value ≤ cur0 + 1 at hcur1Hi
  change st1.mem cur0 + dynGraphSize vCap eCap ≤ cur0 at hGPtrEnd1
  have hSp3 : o3.value ≤ cur0 + op3Space := by omega
  let tok1 : SolverToken cfg L Rcore :=
    { tokFull.1.1 with
      coreTok := Function.update tokFull.1.1.coreTok j y1
      owned := fun a => tokFull.1.1.owned a ∨ (cur0 ≤ a ∧ a < o3.value)
      tag := fun a => if cur0 ≤ a ∧ a < o3.value then 21 + j else tokFull.1.1.tag a }
  obtain ⟨hrep1, hft1, hphi1⟩ :=
    solverStateRep_update_coreTok hlocalCore hjLt hrepFull.1.1 hFootBelow hFr1Out hrep1Core hFoot1
  have hown1 : ∀ a, tokFull.1.1.owned a → tok1.owned a := fun _ ha => Or.inl ha
  have htag1 : ∀ a, tokFull.1.1.tag a ≠ 0 → tok1.tag a = tokFull.1.1.tag a := fun a hne => by
    dsimp only [tok1]
    exact ite_eq_right (by have := hFootBelow a (Or.inl (hOwn0 a hne)); omega)
  let tokFull1 : Rfull.τ := ((tok1, tokFull.1.2), tokFull.2)
  have hrep1Full : Rfull.rep root model tokFull1 st1.mem :=
    ⟨⟨hrep1, hrepFull.1.2.1, hrepFull.1.2.2⟩,
      ⟨⟨hrepFull.2.1.1.1, hrepFull.2.1.1.2⟩,
        hrepFull.2.1.2.1, hrepFull.2.1.2.2.1, hrepFull.2.1.2.2.2⟩,
      hrepFull.2.2.1, hrepFull.2.2.2⟩
  have hphi1Full : c3 + Rfull.phi root tokFull1 st1.mem ≤ Psc.readout + Rfull.phi root tokFull mem := by
    rw [solverStateRepFull_phi_eq hrep1Full.1 hrep1Full.2.2.1 hrep1Full.2.2.2,
      solverStateRepFull_phi_eq hrepFull.1 hrepFull.2.2.1 hrepFull.2.2.2]
    dsimp only [tokFull1, tok1]
    change c3 + Rcore.phi _ y1 st1.mem ≤ Psc.readout + Rcore.phi _ _ mem at hcost3
    omega
  have hcaps1 : SolverLevelCapsInv P V vCap eCap model tok1 st1.mem :=
    hcaps.preserve rfl (fun i hi => hown1 _ (hcaps.1.2.1 i hi))
      (fun a ha => by
        have hne : tokFull.1.1.tag a ≠ 0 := by rcases ha with h | h | h | h <;> omega
        have hnc : ¬ Rcore.foot (tokFull.1.1.coreHandle j) (tokFull.1.1.coreTok j) a := fun hc => by
          have := hCoreTags j hjLt a hc; rcases ha with h | h | h | h <;> omega
        exact ⟨htag1 a hne, hFr1Out a (hFootBelow a (Or.inl (hOwn0 a hne))) hnc⟩)
      (fun i hi => hown1 _ (SolverLevelMetaAt.atCaps hcaps.1 hcaps.2 i hi).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  have hFoot1Lt : ∀ a, Rfull.foot root tokFull1 a → a < o3.value := fun a ha => by
    rcases hft1 a ha with h0 | hnew
    · exact lt_of_lt_of_le (hFootBelow a h0) hcur1Lo
    · exact hnew.2
  have hDgSz : dynGraphSize vCap eCap = 4 + 7 * vCap + 9 * eCap := rfl
  obtain ⟨bE, hbE, oE, st2, cE, hrE, hpE, hcE⟩ :=
    hDgEmpty [o3.value, vCap, eCap] st1.mem st1.pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl) <;> omega)
      ⟨o3.value, vCap, eCap, rfl, by omega, by omega, hz1⟩
  obtain ⟨_, _, _, hargsE, _, hEmpty2, hFr2, hz2_4⟩ := hpE
  simp only [List.cons.injEq] at hargsE; obtain ⟨rfl, rfl, rfl, -⟩ := hargsE
  have hz2 : ZeroFrom st2.mem (o3.value + dynGraphSize vCap eCap) := fun a ha => hz2_4 a (by omega)
  have hDG1_2 : DynGraphAt st2.mem (st1.mem cur0) vCap eCap (model.chain.G cfg.P.d) :=
    DynGraphAt.of_agree hDG1 fun a _ ha2 => hFr2 a (Or.inl (by omega))
  obtain ⟨bC, hbC, oC, st3, cC, hrC, hpC, hcC⟩ :=
    hDgCopy [o3.value, st1.mem cur0, o3.value + dynGraphSize vCap eCap] st2.mem st2.pos ω
      (by simp only [List.mem_cons, List.not_mem_nil, or_false]; rintro v (rfl|rfl|rfl) <;> omega)
      ⟨o3.value, st1.mem cur0, o3.value + dynGraphSize vCap eCap, rfl, hw16, le_refl _,
        by omega, Or.inl (by omega), hEmpty2, hDG1_2, hVcapD, hEcapD, hz2, by omega⟩
  obtain ⟨hoCEq, hGd3, hz3, hFr3⟩ := hpC
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hoCEq hcC hFr3
  have hFr31 : ∀ a < o3.value, st3.mem a = st1.mem a := fun a ha =>
    (hFr3 a (by omega) (Or.inl ha)).trans (hFr2 a (Or.inl ha))
  have hRfullLocal := solverStateRepFull_local cfg κ G L P m V psi k epsExp drainUnit unit toolMul
    treeMul hlocalCore
  have hrep3Full : Rfull.rep root model tokFull1 st3.mem :=
    (hRfullLocal root model tokFull1 st1.mem st3.mem fun a ha => (hFr31 a (hFoot1Lt a ha)).symm).1 hrep1Full
  have hphi3Full : Rfull.phi root tokFull1 st3.mem = Rfull.phi root tokFull1 st1.mem :=
    ((hRfullLocal root model tokFull1 st1.mem st3.mem fun a ha => (hFr31 a (hFoot1Lt a ha)).symm).2).symm
  have hcaps3 : SolverLevelCapsInv P V vCap eCap model tok1 st3.mem :=
    hcaps1.preserve rfl hcaps1.1.2.1
      (fun a ha => ⟨rfl, hFr31 a (hFoot1Lt a (Or.inl (hrep1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 a
        (by intro h0; rcases ha with h | h | h | h <;> rw [h] at h0 <;> omega))))⟩)
      (fun i hi => (SolverLevelMetaAt.atCaps hcaps1.1 hcaps1.2 i hi).2.2.1)
      rfl (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) rfl
  refine ⟨b3, o3, st1, c3, bE, oE, st2, cE, bC, oC, st3, cC, tokFull1,
    hb3, hr3, hbE, hrE, hbC, hrC, hcur1Lo, hSp3, hoCEq, hrep3Full,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hcaps3, hGd3,
    fun a ha hnc => (hFr31 a (by omega)).trans (hFr1Out a ha hnc), hft1, hz3, ?_⟩
  change cE ≤ 40 at hcE
  change cC ≤ dgCopyRefillCost 0 0 (model.chain.G cfg.P.d).n (model.chain.G cfg.P.d).m at hcC
  rw [hphi3Full]; omega

end MinCostFlow.MinRatio
