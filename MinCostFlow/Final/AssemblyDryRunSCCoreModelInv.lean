module

public import MinCostFlow.Final.AssemblyDryRunSCDeepSelectFits
public import MinCostFlow.Final.AssemblyDryRunSCDeepInv
public import MinCostFlow.Final.AssemblyDryRunSCConnected
public import MinCostFlow.MinRatio.WireChainCoreSpecKFBL
public import MinCostFlow.MinRatio.WireChainCoreSelAdapt
public import MinCostFlow.MinRatio.SelectUpdateModel
public import MinCostFlow.MinRatio.SolverTreeBudgetInv
import MinCostFlow.MinRatio.ShiftDeepModelFacts
import Mathlib.Tactic

/-!
# Model-invariant and forest-sum adapters for select-aware `Update` (`AssemblyDryRunSCCoreModelInv`)

Proves the chain-update core model adapters needed to invoke `OrdChainUpdateCoreSpecWExtKFBL`
(`MinRatio/WireChainCoreSpecKFBL.lean`) from the premises of `OrdChainUpdateCoreSpecWKFBLSel`
(`MinRatio/OrdSelSpecs.lean`):

1. `dryCoreSel_forestEdgeSum_le`: unconditionally proves
   `graphListEdgeSum (chainSuffixForests model.chain 0) +
    graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤ 2 * (model.chain.G 0).n`.
2. `dryCoreSel_updateCoreModelInvKFBL`: unconditionally proves all 13 conjuncts of
   `UpdateCoreModelInvKFBL model U gVec lVec` from `ShiftLoopChainInv` before and after `Update`.
3. `CoreSelMetaDisjInv`, `CoreSelVecValidInv`, and `CoreSelMetaDisjInv.rootECap_eq`: captures the
   layout and limb-validity clauses that are between `OrdChainUpdateCoreSpecWKFBLSel` and
   `UpdateCoreModelInv` (showing that `mem0 (levelMeta + d) = tok.rootGraph` immediately implies
   `tok.rootECap = eCap` via `dynGraphAt_caps_eq`).
4. `dryCoreSel_updateCoreModelInv`: proves the full `UpdateCoreModelInv` from the premises of
   `OrdChainUpdateCoreSpecWKFBLSel` together with `CoreSelMetaDisjInv`, `CoreSelVecValidInv`, and
   `UpdateLoopModelInv`.
-/

@[expose] public noncomputable section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- Level-metadata root identity and pairwise disjointness of the level-graph and length-table
blocks in `solverLevelMetaAddr tok.table cfg.P.d` (required by `UpdateCoreModelInv`,
`WireChainSpecs.lean:553, 566-572`, and omitted from `SolverLevelMetaAt`). -/
def CoreSelMetaDisjInv {cfg : Alg2Config} {L : ℕ} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    (vCap eCap : ℕ) (tok : SolverToken cfg L Rcore) (mem0 : ℕ → ℕ) : Prop :=
  let d := cfg.P.d
  let levelMeta := solverLevelMetaAddr tok.table d
  mem0 (levelMeta + d + 0) = tok.rootGraph ∧
  (∀ j < d, ∀ a, mem0 (levelMeta + d + j) ≤ a →
    a < mem0 (levelMeta + d + j) + dynGraphSize vCap eCap →
    ∀ r < d,
      (a < mem0 (levelMeta + r) ∨ mem0 (levelMeta + r) + eCap * L ≤ a) ∧
      (r ≠ j → a < mem0 (levelMeta + d + r) ∨
        mem0 (levelMeta + d + r) + dynGraphSize vCap eCap ≤ a)) ∧
  (∀ j₁ < d, ∀ j₂ < d, j₁ ≠ j₂ →
    mem0 (levelMeta + j₁) + eCap * L ≤ mem0 (levelMeta + j₂) ∨
    mem0 (levelMeta + j₂) + eCap * L ≤ mem0 (levelMeta + j₁))

/-- Limb validity (`Num.Valid`) for the external gradient and length arrays `g` and `l` on every
edge inserted by `U` (required by `UpdateCoreModelInv`, `WireChainSpecs.lean:585-586`, and
supplied by `minRatioMachineContractAt` / `copyInsertedStmt` in `UpdateAssemblySel.lean`). -/
def CoreSelVecValidInv (L g l : ℕ) (U : List Update) (mem0 : ℕ → ℕ) : Prop :=
  ∀ u ∈ U, ∀ e, u.Inserts e → Num.Valid mem0 (g + e * L) 4 L ∧ Num.Valid mem0 (l + e * L) 4 L

end MinCostFlow.Final.DryRun

end

public section

namespace MinCostFlow.Final.DryRun

open WordRAM LinkCut _root_.MinCostFlow.Bundle Chain Chain.Ordered IPM IPM.Machine SparseCore
  SparseCore.Program Scaling Scaling.Machine MinRatio LastLevelProgram DynSpanner.Program

/-- `mem0 (levelMeta + d + 0) = tok.rootGraph` (the first clause of `CoreSelMetaDisjInv`) together
with `SolverLevelCapsAt vCap eCap` and `0 < cfg.P.d` forces `model.extG.n = vCap` and
`tok.rootECap = eCap`. -/
theorem CoreSelMetaDisjInv.rootECap_eq {cfg : Alg2Config} {L P m V psi k epsExp drainUnit
    vCap eCap root : ℕ} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)}
    {model : Alg2State cfg} {tok : SolverToken cfg L Rcore} {mem0 : ℕ → ℕ}
    (hdPos : 0 < cfg.P.d)
    (hrep : (solverStateRep cfg L P m V psi k epsExp drainUnit Rcore).rep root model tok mem0)
    (hcaps : SolverLevelCapsAt vCap eCap model tok mem0)
    (hMetaDisj : CoreSelMetaDisjInv vCap eCap tok mem0) :
    model.extG.n = vCap ∧ tok.rootECap = eCap := by
  have hWire : SolverWireInv P model tok mem0 :=
    hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hDG0 : DynGraphAt mem0 tok.rootGraph model.extG.n tok.rootECap (model.chain.G 0) :=
    hWire.2.1
  have hCap0 : DynGraphAt mem0 (mem0 (solverLevelMetaAddr tok.table cfg.P.d + cfg.P.d + 0))
      vCap eCap (model.chain.G 0) := by
    simpa [Nat.add_zero] using hcaps 0 hdPos
  rw [hMetaDisj.1] at hCap0
  exact dynGraphAt_caps_eq hDG0 hCap0

private lemma isEdgeUpdate_of_refreshBatch {G : MGraph} {U : List Update}
    (hRef : RefreshBatch G U) : ∀ u ∈ U, IsEdgeUpdate u := fun u hu => by
  have hns := hRef.2.2 u hu
  cases u with
  | insert _ _ _ => trivial
  | delete _ => trivial
  | split _ _ _ _ => exact absurd hns id

private lemma applyBatch_V_eq_of_isEdge {G : MGraph} :
    ∀ {U : List Update}, (∀ u ∈ U, IsEdgeUpdate u) → (G.applyBatch U).V = G.V
  | [], _ => rfl
  | u :: rest, hEdge => by
    have h1 : (G.applyUpdate u).V = G.V := by
      have hu := hEdge u (List.mem_cons_self ..)
      cases u <;> simp [IsEdgeUpdate, MGraph.applyUpdate] at hu ⊢
    exact (applyBatch_V_eq_of_isEdge fun x hx => hEdge x (List.mem_cons_of_mem _ hx)).trans h1

/-- **Unconditional forest-edge sum bound for `Update`:** the combined edge count of the old and
new chain suffix forests from level `0` is at most `2 * (model.chain.G 0).n`. -/
theorem dryCoreSel_forestEdgeSum_le {cfg : Alg2Config}
    (hV : cfg.ValidOrdNoHidden)
    {model : Alg2State cfg} {U : List Update} {gVec lVec : ℕ → ℝ}
    (_hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh)
    (hRef : RefreshBatch model.extG U)
    (hShift0 : ShiftLoopChainInv cfg model.chain)
    (hShift1 : ShiftLoopChainInv cfg (alg2PreResetState cfg model U gVec lVec).chain) :
    let modelPre := alg2PreResetState cfg model U gVec lVec
    graphListEdgeSum (chainSuffixForests model.chain 0) +
      graphListEdgeSum (chainSuffixForests modelPre.chain 0) ≤
      2 * (model.chain.G 0).n := by
  intro modelPre
  have h1 := chainSuffixForests_edgeSum_le_G0_n hV hShift0.1 (Nat.zero_le _)
  have h2 := chainSuffixForests_edgeSum_le_G0_n hV hShift1.1 (Nat.zero_le _)
  set tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
  have hEdgeInt : ∀ u ∈ tr.2.2.2.2, IsEdgeUpdate u :=
    translateBatch_isEdgeUpdate model.extG model.extToInt model.intToExt model.nextFresh U
      (isEdgeUpdate_of_refreshBatch hRef)
  have hVnEq : ((model.chain.G 0).applyBatch tr.2.2.2.2).V = (model.chain.G 0).V :=
    applyBatch_V_eq_of_isEdge hEdgeInt
  have hPreN : (modelPre.chain.G 0).n = (model.chain.G 0).n := by
    rcases algorithm1_update_G0_and_g cfg.T cfg.L cfg.TP cfg.P cfg.N₀ model.chain tr.2.2.2.2
        (fun e' => gVec (tr.2.2.1 e')) (fun e' => lVec (tr.2.2.1 e')) with
      ⟨_, hG0, _⟩ | ⟨_, hG0, _⟩
    · have hG0' : modelPre.chain.G 0 = ((model.chain.G 0).applyBatch tr.2.2.2.2).compact := hG0
      rw [hG0']; unfold MGraph.n MGraph.compact; dsimp only; rw [hVnEq]
    · have hG0' : modelPre.chain.G 0 = (model.chain.G 0).applyBatch tr.2.2.2.2 := hG0
      rw [hG0']; unfold MGraph.n; rw [hVnEq]
  dsimp only [modelPre] at hPreN ⊢
  omega

/-- **Unconditional `UpdateCoreModelInvKFBL` adapter:** every one of the 13 conjuncts of
`UpdateCoreModelInvKFBL` follows from `cfg.ValidOrdNoHidden`, `ShiftLoopChainInv` before and
after `Update`, and `∀ j < cfg.P.d, model.chain.bran j < cfg.P.k`. -/
theorem dryCoreSel_updateCoreModelInvKFBL {cfg : Alg2Config}
    (hV : cfg.ValidOrdNoHidden)
    {model : Alg2State cfg} {U : List Update} {gVec lVec : ℕ → ℝ}
    (hShift0 : ShiftLoopChainInv cfg model.chain)
    (hShift1 : ShiftLoopChainInv cfg (alg2PreResetState cfg model U gVec lVec).chain)
    (hBr : ∀ j < cfg.P.d, model.chain.bran j < cfg.P.k) :
    UpdateCoreModelInvKFBL model U gVec lVec := by
  set modelPre := alg2PreResetState cfg model U gVec lVec
  have hB0 := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hShift0.1
  have hB1 := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hShift1.1
  have hH0 := (hShift0.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hH1 := (hShift1.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hDisjOf : ∀ {ch : ChainState cfg.T cfg.P} {σ σ_mwu γ_ℓ γ_c : ℝ},
      ch.toTreeChain.Holds (ch.G 0) ch.ℓ σ σ_mwu γ_ℓ γ_c →
      ∀ j₁ ≤ cfg.P.d, ∀ j₂ ≤ cfg.P.d, j₁ ≠ j₂ →
        Disjoint (ch.toTreeChain.activeLSF j₁).F.F.E (ch.toTreeChain.activeLSF j₂).F.F.E := by
    intro ch σ σ_mwu γ_ℓ γ_c hH j₁ hj1 j₂ hj2 hne
    have hltPair : ∀ a b, a < b → b ≤ cfg.P.d →
        Disjoint (ch.toTreeChain.activeLSF a).F.F.E (ch.toTreeChain.activeLSF b).F.F.E := fun a b hab hbd =>
      Finset.disjoint_of_subset_left
        (Finset.subset_biUnion_of_mem (fun j => (ch.toTreeChain.activeLSF j).F.F.E)
          (Finset.mem_range.mpr hab))
        (initChain_prefix_disjoint hH hbd)
    rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
    · exact hltPair j₁ j₂ hlt hj2
    · exact (hltPair j₂ j₁ hgt hj1).symm
  refine ⟨shiftLoopLevelFacts_of_inv hV hShift0, shiftLoopLevelFacts_of_inv hV hShift1,
    fun j hj => ⟨(hB0 j hj).1, (hB1 j hj).1⟩,
    fun j hj => (Finset.card_le_card (hB1 j hj).2.1).trans (hShift1.1.hN0 ▸ hShift1.1.hG0n),
    fun j hj => chainInv_ordRotWords_live_le hV hShift1.1 hj,
    fun j hj => ?_,
    (hShift0.1.hLastHolds model.chain.lastBran hShift0.1.hLastBran).2.1.2.2.2.2.2.1,
    (hShift1.1.hLastHolds modelPre.chain.lastBran hShift1.1.hLastBran).2.1.2.2.2.2.2.1,
    by exact_mod_cast (hB0 cfg.P.d le_rfl).2.2.1,
    by exact_mod_cast (hB1 cfg.P.d le_rfl).2.2.1,
    hBr, hDisjOf hH0, hDisjOf hH1,
    fun j hj => by exact_mod_cast (hB1 j hj).2.2.1,
    (ChainInv.levels_connected hV.hTP hV.hγM₀ hV.hγk hShift1.1 hShift1.2.2.2 cfg.P.d le_rfl).1⟩
  have hAct0 := (hB0 j (Nat.le_of_lt hj)).2.2.2.2 hj (model.chain.bran j) (hShift0.1.hBran j hj)
  have hAct1 := (hB1 j (Nat.le_of_lt hj)).2.2.2.2 hj (modelPre.chain.bran j) (hShift1.1.hBran j hj)
  exact ⟨le_of_eq hAct0.1.2.1.2.1, hAct0.1.2.1.2.2.2.2.2.1, chainInv_G_succ_E_subset hV hShift0.1 hj,
    hAct1.1.2.1.2.2.2.2.2.1, chainInv_G_succ_E_subset hV hShift1.1 hj⟩

private lemma ipmQuality_arith_cm (m V k : ℕ) :
    let L := ipmQualityLimbs m V k
    let P := ipmQualityPrecision m V k
    let epsExp := k + Num.IPM.alphaExponent m V + 10
    P ≤ 4 * L ∧ 4 ∣ P ∧ 0 < L ∧ epsExp ≤ P ∧ P - epsExp + 1 < 4 * L := by
  have hk : k ≤ qualitySlackExponent m V k := qualityExponent_le_qualitySlackExponent m V k
  have hα : Num.IPM.alphaExponent m V ≤ Num.IPM.alphaScale m V := by
    unfold Num.IPM.alphaExponent Num.IPM.alphaScale
    have hc : Nat.clog 2 (1000 * (m.size + V.size)) ≤ 1000 * (m.size + V.size) :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr Nat.lt_two_pow_self.le
    omega
  dsimp only [ipmQualityLimbs, ipmQualityPrecision, ipmQualityErrorBits, ipmQualityRangeExponent]
  exact ⟨by omega, Nat.dvd_mul_right 4 _, by omega, by omega, by omega⟩

private lemma cfg_eps_eq_cm (J : Circulation) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let P := ipmQualityPrecision I.m V k
    let epsExp := k + Num.IPM.alphaExponent I.m V + 10
    (concreteCirculationCfgWithLast dryWitnessUsed J).ε =
      ((2 : ℤ) ^ (P - epsExp) : ℝ) / (2 : ℝ) ^ P := by
  intro I V k P epsExp
  have hle : epsExp ≤ P := (ipmQuality_arith_cm I.m V k).2.2.2.1
  dsimp only [concreteCirculationCfgWithLast, concreteCirculationCfgOfDims,
    Chain.Ordered.concreteAlg2CfgWithLast, Num.IPM.alphaPrime]
  have h1024 : (1024 : ℝ) = (2 : ℝ) ^ (10 : ℕ) := by norm_num
  have h2pos : (0 : ℝ) < (2 : ℝ) ^ P := by positivity
  have h2e : (0 : ℝ) < (2 : ℝ) ^ epsExp := by positivity
  have hpow : (2 : ℝ) ^ (P - epsExp) * (2 : ℝ) ^ epsExp = (2 : ℝ) ^ P := by
    rw [← pow_add, Nat.sub_add_cancel hle]
  push_cast
  rw [eq_div_iff h2pos.ne', h1024]
  calc (1 / (2 : ℝ) ^ k) * (1 / (2 : ℝ) ^ Num.IPM.alphaExponent I.m V) / (2 : ℝ) ^ 10 *
        (2 : ℝ) ^ P
      = (2 : ℝ) ^ P /
          ((2 : ℝ) ^ k * (2 : ℝ) ^ Num.IPM.alphaExponent I.m V * (2 : ℝ) ^ 10) := by ring
    _ = (2 : ℝ) ^ P / (2 : ℝ) ^ epsExp := by
        dsimp only [epsExp]; rw [pow_add, pow_add]
    _ = (2 : ℝ) ^ (P - epsExp) := by rw [div_eq_iff h2e.ne', hpow]

private lemma fits_of_abs_le_B_cm {L n : ℕ} {B R z : ℤ}
    (hB0 : 0 ≤ B) (hR0 : 0 ≤ R)
    (hFit : 2 * ((2 * n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 L : ℤ))
    (hz : |z| ≤ B) : Num.Fits 4 L z := by
  have hn1 : (1 : ℤ) ≤ ((2 * n + 1 : ℕ) : ℤ) := by omega
  have hBR : 2 * (B + R) ≤ 2 * ((2 * n + 1 : ℕ) : ℤ) * (B + R) := by nlinarith
  have h2B : 2 * B < (Num.capacity 4 L : ℤ) := by linarith
  unfold Num.Fits
  rw [abs_le] at hz
  omega

private lemma not_mem_applyBatch_of_not_inserts {e : ℕ} :
    ∀ {U : List Update} {G : MGraph}, e ∉ G.E → (∀ u ∈ U, ¬ u.Inserts e) → e ∉ (G.applyBatch U).E
  | [], _, hnot, _ => hnot
  | u :: rest, G, hnot, hno => by
    have h1 : e ∉ (G.applyUpdate u).E := by
      have hu := hno u List.mem_cons_self
      cases u with
      | insert e' _ _ =>
        simp only [MGraph.applyUpdate, Finset.mem_insert, not_or]
        exact ⟨fun heq => hu (heq ▸ rfl), hnot⟩
      | delete e' =>
        simp only [MGraph.applyUpdate, Finset.mem_erase, not_and]
        exact fun _ => hnot
      | split _ _ _ _ => exact hnot
    exact not_mem_applyBatch_of_not_inserts (U := rest) (G := G.applyUpdate u) h1
      (fun v hv => hno v (List.mem_cons_of_mem _ hv))

private lemma batch_delete_not_mem_applyBatch {e : ℕ} :
    ∀ {U : List Update} {G : MGraph},
      (∀ u ∈ U, ¬ u.Inserts e) → Update.delete e ∈ U → e ∉ (G.applyBatch U).E
  | [], _, _, hmem => by cases hmem
  | u :: rest, G, hno, hmem => by
    rcases List.mem_cons.mp hmem with rfl | hrest
    · exact not_mem_applyBatch_of_not_inserts (U := rest) (G := G.applyUpdate (.delete e))
        (by simp [MGraph.applyUpdate]) (fun v hv => hno v (List.mem_cons_of_mem _ hv))
    · exact batch_delete_not_mem_applyBatch (U := rest) (G := G.applyUpdate u)
        (fun v hv => hno v (List.mem_cons_of_mem _ hv)) hrest

private lemma mem_refreshBatch_inserts_of_delete_int {G H : MGraph}
    {e2i i2e : ℕ → ℕ} {nf : ℕ} {U : List Update}
    (hFresh : FreshInv G H e2i i2e nf) (hRef : RefreshBatch G U)
    {ei_old : ℕ} (heiOld : ei_old ∈ H.E)
    (hDel : Update.delete ei_old ∈ (translateBatch G e2i i2e nf U).2.2.2.2) :
    let tr := translateBatch G e2i i2e nf U
    let e := tr.2.2.1 ei_old
    e ∈ G.E ∧ ∃ u ∈ U, u.Inserts e := by
  intro tr e
  have hTr := translateBatch_preserves U G H e2i i2e nf hFresh hRef.1
  dsimp only at hTr
  have hlt : ei_old < nf := hFresh.hLtFresh ei_old heiOld
  have hI2E : tr.2.2.1 ei_old = i2e ei_old := hTr.2.2.2.2.2.2.2.1 ei_old hlt
  have hRight := hFresh.hRight ei_old heiOld
  have heG : e ∈ G.E := by dsimp only [e]; rw [hI2E]; exact hRight.2
  have hnotH' : ei_old ∉ (H.applyBatch tr.2.2.2.2).E :=
    batch_delete_not_mem_applyBatch (hTr.2.2.2.1 ei_old heiOld) hDel
  have hExtEq : tr.1 = G := hTr.1.trans hRef.2.1
  have hInTr : e ∈ tr.1.E := hExtEq.symm ▸ heG
  have hInsExt : ∃ u ∈ U, u.Inserts e := by
    by_contra hNo
    push Not at hNo
    have hSame := hTr.2.2.2.2.2.2.2.2.1 e hInTr hNo
    have hE2I : tr.2.1 e = ei_old := by
      rw [hSame.2.1]; dsimp only [e]; rw [hI2E]; exact hRight.1
    have hInH' : tr.2.1 e ∈ (H.applyBatch tr.2.2.2.2).E :=
      hTr.2.1.hE ▸ Finset.mem_image_of_mem _ hInTr
    rw [hE2I] at hInH'
    exact hnotH' hInH'
  exact ⟨heG, hInsExt⟩

/-- **Full `UpdateCoreModelInv` adapter:** proves every conjunct of `UpdateCoreModelInv` from the
premises of `OrdChainUpdateCoreSpecWKFBLSel` together with `CoreSelMetaDisjInv`,
`CoreSelVecValidInv`, and `UpdateLoopModelInv`. -/
theorem dryCoreSel_updateCoreModelInv
    (J : Circulation) (hJn : J.n ≤ 2 * J.m + 1) (hJm : 0 < J.m) (hCap1 : ∀ e, 1 ≤ J.capacity e)
    {w wordExp stretchPrec : ℕ}
    (hw : ipmQualityParameterWordBits (solverConnectedAugmented J).m (solverPenalty J.m)
      (cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
        (concreteQualityBudgetWithLast dryWitnessUsed) (solverConnectedAugmented J).m) ≤ w) :
    let I := solverConnectedAugmented J
    let V := solverPenalty J.m
    let k := cappedQualityExponent (concreteEdgeThresholdWithLast dryWitnessUsed)
      (concreteQualityBudgetWithLast dryWitnessUsed) I.m
    let F := ipmQualityMinRatioFormat I.m V k hw
    let cfg := concreteCirculationCfgWithLast dryWitnessUsed J
    let G := namedInstance I
    let epsExp := k + Num.IPM.alphaExponent I.m V + 10
    ∀ {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {root _uIntBuf g l : ℕ}
      {mem0 : ℕ → ℕ} {model : Alg2State cfg} {tok : SolverToken cfg F.limbs Rcore}
      {sg : SelectGhost} {U : List Update} {B R : ℤ},
      let Rrep := solverStateRep cfg F.limbs F.fmt.precision I.m V ⌈cfg.Ψ⌉₊ k epsExp
        (detectOffTreeDrainUnit F.limbs) Rcore
      let tr := translateBatch model.extG model.extToInt model.intToExt model.nextFresh U
      let gVec := updateOverlay model.extG.E U (readVector mem0 g 4 F.limbs F.fmt.precision I.m) model.extg
      let lVec := updateOverlay model.extG.E U (readVector mem0 l 4 F.limbs F.fmt.precision I.m) model.extℓ
      let modelPre := alg2PreResetState cfg model U gVec lVec
      Rrep.rep root model tok mem0 →
      SolverLevelMetaAt F.fmt.precision V model tok mem0 →
      SolverLevelCapsAt G.n (initTargetCap cfg G) model tok mem0 →
      OrdSolverReached cfg (1 / (2 : ℝ) ^ k) G model →
      PathTreeNumericInv tok.tree tok.trees B R →
      treeBudgetBase F.fmt.precision F.rangeExponent ≤ B →
      2 * ((2 * model.extG.n + 1 : ℕ) : ℤ) * (B + R) < (Num.capacity 4 F.limbs : ℤ) →
      (∀ e ∈ model.extG.E, |model.extg e| ≤ (2 : ℝ) ^ F.rangeExponent ∧
        (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ model.extℓ e ∧ model.extℓ e ≤ (2 : ℝ) ^ F.rangeExponent) →
      (∀ e ∈ model.extG.E, 0 ≤ model.detectAccum e ∧ model.extℓ e * model.detectAccum e < cfg.ε) →
      tok.intCap = initTargetCap cfg G →
      ShiftLoopChainInv cfg model.chain →
      ShiftLoopChainInv cfg modelPre.chain →
      (∀ e ∈ model.extG.E, |gVec e| ≤ (2 : ℝ) ^ F.rangeExponent ∧
        (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ lVec e ∧ lVec e ≤ (2 : ℝ) ^ F.rangeExponent) →
      tr.2.2.2.1 ≤ tok.intCap →
      RefreshBatch model.extG U →
      (∀ j < I.m * F.limbs, ¬ (Rrep.foot root tok (g + j) ∨ sg.owned (g + j)) ∧
        ¬ (Rrep.foot root tok (l + j) ∨ sg.owned (l + j))) →
      CoreSelMetaDisjInv G.n (initTargetCap cfg G) tok mem0 →
      CoreSelVecValidInv F.limbs g l U mem0 →
      UpdateLoopModelInv w F.limbs F.fmt.precision wordExp stretchPrec
        (fun _ => G.n) (fun _ => initTargetCap cfg G)
        (fun j => model.chain.toTreeChain.chainLen model.chain.ℓ j)
        (fun e' => lVec (tr.2.2.1 e')) (fun e' => gVec (tr.2.2.1 e')) cfg.P.d 0
        { model.chain with
          recUpdates := fun j =>
            if j = 0 then model.chain.recUpdates 0 + tr.2.2.2.2.length
            else model.chain.recUpdates j }
        ((model.chain.G 0).applyBatch tr.2.2.2.2) tr.2.2.2.2
        ((model.chain.G 0).batchEnc tr.2.2.2.2) (model.chain.levelOrd 0) →
      UpdateCoreModelInv w F.limbs F.fmt.precision I.m epsExp wordExp stretchPrec
        model tok U mem0 g l B := by
  intro I V k F cfg G epsExp Rcore root uIntBuf g l mem0 model tok sg U B R
    Rrep tr gVec lVec modelPre
    hrep hMeta hCaps hReach hTreeNum hB0 hFitTree hExtGLRng hDet hICap hShift0 hShift1 hGLRng
    hnfCap hRef hVecOff hMetaDisj hVecValid hLoopModel
  have hV : cfg.ValidOrdNoHidden :=
    concreteCirculationCfgWithLast_validOrdNoHidden dryWitnessUsed J hJn hJm hCap1
  have hImPos : 0 < I.m := lt_of_lt_of_le hJm (solverConnectedAugmented_size J hJn hJm hCap1).1
  have hdPos : 0 < cfg.P.d := cfg.P.hd
  have hArith := ipmQuality_arith_cm I.m V k
  have hEpsEq := cfg_eps_eq_cm J
  have hFresh : FreshInv model.extG (model.chain.G 0) model.extToInt model.intToExt model.nextFresh :=
    hrep.2.2.2.2.1
  have hExtLtM : ∀ e ∈ model.extG.E, e < I.m := hrep.2.2.2.2.2.2.1
  obtain ⟨hExtN_eq, hRootECapEq⟩ := CoreSelMetaDisjInv.rootECap_eq hdPos hrep hCaps hMetaDisj
  -- Extract `model.extG = G` and `model.chain.ℓ ei = model.extℓ (model.intToExt ei)` from `hReach`
  obtain ⟨hExtG_eq, hChℓ, hExtNLe⟩ :
      model.extG = G ∧
      (∀ ei ∈ (model.chain.G 0).E, model.chain.ℓ ei = model.extℓ (model.intToExt ei)) ∧
      model.extG.n ≤ cfg.N₀ := by
    obtain ⟨_, _, _, _, hIn⟩ := concreteCirculation_bounds_of
      (le_max_left dryWitnessUsed.M_thresh _) (le_max_right dryWitnessUsed.M_thresh _)
      (concreteEdgeThresholdWithLast_ge_two dryWitnessUsed) J hJn hJm hCap1
    have hmG : G.m ≤ cfg.P.M₀ := by rw [namedInstance_m]; exact le_max_left _ _
    have hnG : G.n ≤ cfg.N₀ := by
      have hInEq : G.n = I.n := by simp [G, namedInstance, MGraph.n]
      rw [hInEq]; exact hIn
    obtain ⟨D, η, op, T_step, hHist, hEdgeD, hLenD, hGD, hEq⟩ := hReach
    have hUncond := (algorithm2_uncond_preserves_with (η := η) (1 / (2 : ℝ) ^ k) hV hHist hEdgeD
      hLenD (fun t ht => by rw [hGD t ht]; exact hmG) (fun t ht => by rw [hGD t ht]; exact hnG)).1
      T_step le_rfl
    rw [← hEq] at hUncond
    rcases hUncond with ⟨_, _, _, _, _, hEG, _, hCℓ, _, _, _, _, _, _, _⟩
    have hEGEq : model.extG = G := hEG.trans (hGD T_step le_rfl)
    exact ⟨hEGEq, fun ei _ => congrFun hCℓ ei, hEGEq ▸ hnG⟩
  have hB0_nn : 0 ≤ B := le_trans (by unfold treeBudgetBase; positivity) hB0
  have hR0_nn : 0 ≤ R := hTreeNum.2.1
  have hεPos : 0 < cfg.ε := by
    rw [hEpsEq]; positivity
  have hεLe : cfg.ε ≤ (2 : ℝ) ^ F.rangeExponent := by
    rw [hEpsEq]
    have h1 : ((2 : ℤ) ^ (F.fmt.precision - epsExp) : ℝ) / (2 : ℝ) ^ F.fmt.precision ≤ 1 := by
      rw [div_le_one (by positivity)]
      push_cast
      exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
    exact h1.trans (one_le_pow₀ (by norm_num))
  -- Translate batch properties for caps and `G0'`
  have hTr := translateBatch_preserves U model.extG (model.chain.G 0)
    model.extToInt model.intToExt model.nextFresh hFresh hRef.1
  dsimp only at hTr
  have hG0'LtCap : ∀ e ∈ ((model.chain.G 0).applyBatch tr.2.2.2.2).E, e < tok.intCap := fun e he =>
    lt_of_lt_of_le (hTr.2.1.hLtFresh e he) hnfCap
  have hG0'mLe : ((model.chain.G 0).applyBatch tr.2.2.2.2).m ≤ tok.intCap :=
    (Finset.card_le_card fun e he => Finset.mem_range.mpr (hG0'LtCap e he)).trans (by simp)
  have hBatchCaps : BatchWithinCaps model.extG.n tok.rootECap tr.2.2.2.2 := by
    rw [hRootECapEq, ← hICap]
    refine fun u hu => ?_
    have hEdgeU := translateBatch_isEdgeUpdate model.extG model.extToInt model.intToExt
      model.nextFresh U (isEdgeUpdate_of_refreshBatch hRef) u hu
    cases u with
    | delete e => trivial
    | insert e u' v' =>
      exact lt_of_lt_of_le (hTr.2.2.2.2.2.2.1 (.insert e u' v') hu e rfl).2 hnfCap
    | split _ _ _ _ => simp [IsEdgeUpdate] at hEdgeU
  -- Chain / forest inclusions from `ShiftLoopChainInv`
  have hB0_lvl := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hShift0.1
  have hB1_lvl := Ordered.level_bounds_aux_noHidden cfg.T cfg.L cfg.TP cfg.LP cfg.P cfg.N₀
    hV.hTP hV.hγM₀ hV.hγk hShift1.1
  have hH0 := (hShift0.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hH1 := (hShift1.1.toTreeChain_holds_noHidden hV.hσ_mwu_mono hV.hTP hV.hLP hV.hMWU hV.hEmb
    hV.hγM₀ hV.hγk).1
  have hSub0 := model.chain.toTreeChain.forestsAreSubgraphs_of_holds hH0
  have hSub1 := modelPre.chain.toTreeChain.forestsAreSubgraphs_of_holds hH1
  have hOldSubG0 : model.chain.toTreeChain.chainTree.E ⊆ (model.chain.G 0).E :=
    (model.chain.toTreeChain.chainTree_isSubgraph hH0 hSub0).2.1
  have hNewSubG0 : modelPre.chain.toTreeChain.chainTree.E ⊆ (modelPre.chain.G 0).E :=
    (modelPre.chain.toTreeChain.chainTree_isSubgraph hH1 hSub1).2.1
  have hActiveSub (ch : ChainState cfg.T cfg.P) (j : ℕ) (hj : j ≤ cfg.P.d) :
      (ch.toTreeChain.activeLSF j).F.F.E ⊆ ch.toTreeChain.chainTree.E := fun e he => by
    simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, ChainState.toTreeChain,
      Finset.mem_biUnion, Finset.mem_range]
    exact ⟨j, Nat.lt_succ_of_le hj, he⟩
  -- Assemble all conjuncts of `UpdateCoreModelInv`
  refine ⟨⟨hdPos, hImPos⟩, ⟨hShift0.1.hN0, hExtNLe, by rw [hRootECapEq, hICap]⟩,
    hChℓ,
    updateCore_vecOffFoot_of_not_foot (fun j hj => fun hf => (hVecOff j hj).1 (Or.inl hf))
      (fun j hj => fun hf => (hVecOff j hj).2 (Or.inl hf)),
    fun j hj => (hB1_lvl j hj.le).1,
    ⟨hArith.2.1, hArith.2.2.2.1, hArith.2.2.2.2, hEpsEq⟩,
    ⟨hShift0.1.hLastBran, hShift1.1.hLastK⟩,
    fun j hj => by
      obtain ⟨H⟩ := hShift0.1.hHist j hj
      rw [hShift0.1.hLvlM, hShift0.1.hN0]
      exact levelHistory_sparseCoreOrdInput H,
    ⟨hMetaDisj.1, fun _ => G.n, fun _ => initTargetCap cfg G,
      fun j hj => by
        obtain ⟨hDGj, hLenj, hOwnj, hTj1, hTj2⟩ := hMeta.atCaps hCaps j hj
        exact ⟨hDGj, hLenj, hOwnj, hTj1, fun a ha1 ha2 =>
          ⟨hTj2 a ha1 ha2, hMetaDisj.2.1 j hj a ha1 ha2⟩⟩,
      hMetaDisj.2.2, hLoopModel⟩,
    hBatchCaps,
    fun e he => ⟨by rw [hRootECapEq, ← hICap]; exact hG0'LtCap e he, hG0'LtCap e he⟩,
    by rw [hRootECapEq, ← hICap]; exact hG0'mLe, hG0'mLe, ?_,
    modelPre.chain.toTreeChain.chainTree_isForest hH1 hSub1,
    hOldSubG0, hNewSubG0,
    fun j hj => ⟨Finset.Subset.trans
        (by simpa [TreeChain.activeLSF, ChainState.toTreeChain, hj] using
          hActiveSub model.chain j hj.le) hOldSubG0,
      Finset.Subset.trans
        (by simpa [TreeChain.activeLSF, ChainState.toTreeChain, hj] using
          hActiveSub modelPre.chain j hj.le) hNewSubG0⟩,
    Finset.Subset.trans
      (by simpa [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl] using
        hActiveSub model.chain cfg.P.d le_rfl) hOldSubG0,
    Finset.Subset.trans
      (by simpa [TreeChain.activeLSF, ChainState.toTreeChain, lt_irrefl] using
        hActiveSub modelPre.chain cfg.P.d le_rfl) hNewSubG0⟩
  -- Refreshed-edge numeric & fit bounds
  intro ei_old heiOld hDel
  obtain ⟨heG, uIns, huIns, heIns⟩ := mem_refreshBatch_inserts_of_delete_int hFresh hRef heiOld hDel
  set e := tr.2.2.1 ei_old
  have heM : e < I.m := hExtLtM e heG
  obtain ⟨hVg, hVl⟩ := hVecValid uIns huIns e heIns
  have hgOv : gVec e = readVector mem0 g 4 F.limbs F.fmt.precision I.m e := by
    dsimp only [gVec, updateOverlay]
    rw [ite_eq_right (fun h => h.2 ⟨uIns, huIns, heIns⟩)]
  have hlOv : lVec e = readVector mem0 l 4 F.limbs F.fmt.precision I.m e := by
    dsimp only [lVec, updateOverlay]
    rw [ite_eq_right (fun h => h.2 ⟨uIns, huIns, heIns⟩)]
  have hgVal : ((Num.intVal mem0 (g + e * F.limbs) 4 F.limbs : ℤ) : ℝ) /
      (2 : ℝ) ^ F.fmt.precision = gVec e := by
    rw [hgOv]; simp [readVector, heM, Num.fixVal]
  have hlVal : ((Num.intVal mem0 (l + e * F.limbs) 4 F.limbs : ℤ) : ℝ) /
      (2 : ℝ) ^ F.fmt.precision = lVec e := by
    rw [hlOv]; simp [readVector, heM, Num.fixVal]
  obtain ⟨hgLe, hlLo, hlHi⟩ := hGLRng e heG
  have hlPosR : 0 < lVec e := lt_of_lt_of_le (by positivity) hlLo
  have hlPosZ : 0 < Num.intVal mem0 (l + e * F.limbs) 4 F.limbs := by
    have h1 : (0 : ℝ) < ((Num.intVal mem0 (l + e * F.limbs) 4 F.limbs : ℤ) : ℝ) := by
      have hp : (0 : ℝ) < (2 : ℝ) ^ F.fmt.precision := by positivity
      have := (div_pos_iff_of_pos_right hp).mp (hlVal.symm ▸ hlPosR)
      exact this
    exact_mod_cast h1
  have hgAbsB : |Num.intVal mem0 (g + e * F.limbs) 4 F.limbs| ≤ B :=
    (abs_int_le_base_of_scaled hgVal hgLe).trans hB0
  have hlAbsB : |Num.intVal mem0 (l + e * F.limbs) 4 F.limbs| ≤ B :=
    (abs_int_le_base_of_scaled hlVal (by rw [abs_of_pos hlPosR]; exact hlHi)).trans hB0
  set thrNew := detectorThreshold F.fmt.precision cfg.ε (lVec e)
  obtain ⟨hthr0, hthrHi⟩ := detectorThreshold_range_of_len (P := F.fmt.precision) hεPos hεLe hlLo
  have hthrAbsB : |thrNew| ≤ B :=
    (abs_detectorThreshold_le_base hεPos hεLe hlLo).trans hB0
  have hthrNegFit : Num.Fits 4 F.limbs (-thrNew) :=
    fits_of_abs_le_B_cm hB0_nn hR0_nn hFitTree (by rwa [abs_neg])
  have hthrFit : Num.Fits 4 F.limbs thrNew :=
    fits_of_abs_le_B_cm hB0_nn hR0_nn hFitTree hthrAbsB
  refine ⟨hVg, hVl, hgVal, hlVal, hlPosZ, hgAbsB, hlAbsB, hthrNegFit, hthrFit, ?_⟩
  intro acc hacc
  obtain ⟨hacc0, haccLt⟩ := hDet e heG
  have hOldLenLo : (2 : ℝ) ^ (-(F.rangeExponent : ℤ)) ≤ model.extℓ e := (hExtGLRng e heG).2.1
  have haccDiffB : |acc - thrNew| ≤ B :=
    (abs_detector_le_base hacc hacc0 haccLt hOldLenLo hεLe hthr0 hthrHi).trans hB0
  have haccAbsB : |acc| ≤ B := by
    have h0 := abs_detector_le_base (thr := 0) hacc hacc0 haccLt hOldLenLo hεLe le_rfl (by positivity)
    rw [sub_zero] at h0
    exact h0.trans hB0
  exact ⟨haccDiffB, fits_of_abs_le_B_cm hB0_nn hR0_nn hFitTree haccAbsB,
    fits_of_abs_le_B_cm hB0_nn hR0_nn hFitTree haccDiffB⟩

end MinCostFlow.Final.DryRun

end
