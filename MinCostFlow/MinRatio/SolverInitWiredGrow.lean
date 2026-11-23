module

public import MinCostFlow.MinRatio.SolverInitWiredBase
public import MinCostFlow.MinRatio.InitRootECap
import WordRAM.Tactic

/-!
# Post-threshold table-growth tail of `solverInitWiredBody` (`SolverInitWiredGrow`)

Split out of `SolverInitWiredBase.lean` to keep both files short. Proves `initGrowTablesTail_runs`,
which grows the six `intCap`-indexed internal tables to `newCap` while preserving `solverStateRep`,
`PreservesLevelMeta`, `PathTreeNumericInv`, `OffTreeRecInv`, `OffTreeRecBound`, and potential.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM LinkCut Chain DynSpanner.Program IPM.Machine SparseCore.Program

theorem range_sup_id_add_one {m : ℕ} (hm : 0 < m) :
    (Finset.range m).sup id + 1 = m := by
  have hle : (Finset.range m).sup id ≤ m - 1 :=
    Finset.sup_le fun x hx => by have := Finset.mem_range.mp hx; change x ≤ m - 1; omega
  have hge : m - 1 ≤ (Finset.range m).sup id :=
    Finset.le_sup (f := id) (Finset.mem_range.mpr (by omega))
  omega

theorem ordRebuildSuffix_updCount_zero (T : SparseCoreRestartTool) (L : LastLevelTool)
    (P : ChainParams) (lvlM : ℕ → ℕ) (N₀ : ℕ) (ℓ₀ g₀ : ℕ → ℝ) (i : ℕ) :
    ∀ (rem first : ℕ) (Gf : ℕ → MGraph) (sc : ℕ → T.State) (br ce cd cf : ℕ → ℕ),
      (Chain.Ordered.rebuildSuffix T L P lvlM N₀ ℓ₀ g₀ rem first Gf sc br
        (fun _ => 0) ce cd cf).2.2.2.1 i = 0 := by
  intro rem
  induction rem with
  | zero => intro _ _ _ _ _ _ _; rfl
  | succ rem ih =>
    intro first Gf sc br ce cd cf
    unfold Chain.Ordered.rebuildSuffix; dsimp only
    have hfun : (fun j => if j = first then 0 else (fun _ : ℕ => 0) j) = fun _ => 0 := by
      funext j; split_ifs <;> rfl
    rw [hfun]; exact ih _ _ _ _ _ _ _

/-- When `cfg.N₀ = 4 * cfg.P.M₀`, `0 < m`, `G.E = Finset.range m`, and `m ≤ cfg.P.M₀`, the inline
root edge capacity `initRootECap cfg.N₀ cfg.P.k m` equals `initTargetCap cfg G`. -/
theorem initRootECap_eq_initTargetCap {cfg : Alg2Config} {G : MGraph} {m : ℕ}
    (hN₀Eq : cfg.N₀ = 4 * cfg.P.M₀) (hmPos : 0 < m)
    (hGE : G.E = Finset.range m) (hmLeM₀ : m ≤ cfg.P.M₀) :
    initRootECap cfg.N₀ cfg.P.k m = initTargetCap cfg G := by
  have hGm : G.m = m := by unfold MGraph.m; rw [hGE, Finset.card_range]
  have hsup : G.E.sup id + 1 = m := by rw [hGE]; exact range_sup_id_add_one hmPos
  unfold initRootECap initTargetCap Chain.Ordered.alg2NameBase
  rw [hsup, hGm, max_eq_right hmLeM₀, Chain.intRebuildThreshold_zero_eq, hN₀Eq]
  have h4 : 4 * cfg.P.M₀ / 4 = cfg.P.M₀ := by omega
  rw [h4, sq]

/-- Post-threshold table-growth tail of `solverInitWiredBody`: runs `growIntTablesFromReg7`
to grow the six internal tables to `newCap` and returns `finalHeap + 6 * newCap`. -/
theorem initGrowTablesTail_runs {w L P m V psi k epsExp copyWords root finalHeap initSpace' newCap : ℕ}
    {cfg : Alg2Config} {Rcore : DSRep (SparseCoreOrdAbs cfg.T)} {p : Program} {ω : ℕ → Bool}
    {mem : ℕ → ℕ} {st : State} {s0 : Alg2State cfg} {tok : SolverToken cfg L Rcore} {B_tree : ℤ} {P_gl : Prop}
    (hCopy : MeetsContract w p copyWords (copyWordsContract w)) (hlocal : Rcore.Local)
    (hw14 : 14 ≤ w) (hmPos : 0 < m)
    (hr8 : st.regs 8 = root) (hr9 : st.regs 9 = finalHeap) (hr7 : st.regs 7 = newCap)
    (htokCap : tok.intCap = m) (hcapLt : m < newCap) (hnfLe : s0.nextFresh ≤ m)
    (hExtInt : ∀ e ∈ s0.extG.E, s0.extToInt e < m)
    (hrep : (solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore).rep root s0 tok st.mem)
    (hNum : PathTreeNumericInv tok.tree tok.trees B_tree 0)
    (hoffRec : OffTreeRecInv s0 L st.mem tok.edgeRecords B_tree)
    (hoffBound : P_gl → OffTreeRecBound s0 L st.mem tok.edgeRecords B_tree)
    (hrootLe : root ≤ finalHeap) (hfinLe : finalHeap ≤ root + initSpace')
    (hroom : root + (initSpace' + 6 * newCap) < 2 ^ w)
    (hz : ZeroFrom st.mem finalHeap) (hcaller : ∀ a < root, st.mem a = mem a)
    (hfoot : ∀ a, (solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore).foot root tok a →
      root ≤ a ∧ a < finalHeap) :
    let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
    ∃ cost out tok',
      Runs w p ω
        (.assign 0 (.reg 8) ;; .assign 5 (.load (.bin .add (.reg 0) (.const 15))) ;;
         .assign 8 (.reg 9) ;; growIntTablesFromReg7 copyWords ;; .ret (.reg 14))
        st (.returned (finalHeap + 6 * newCap)) out cost ∧
      Rrep.rep root s0 tok' out.mem ∧ tok'.intCap = newCap ∧
      PreservesLevelMeta tok tok' st.mem out.mem ∧
      PathTreeNumericInv tok'.tree tok'.trees B_tree 0 ∧
      OffTreeRecInv s0 L out.mem tok'.edgeRecords B_tree ∧
      (P_gl → OffTreeRecBound s0 L out.mem tok'.edgeRecords B_tree) ∧
      root ≤ finalHeap + 6 * newCap ∧ finalHeap + 6 * newCap ≤ root + (initSpace' + 6 * newCap) ∧
      ZeroFrom out.mem (finalHeap + 6 * newCap) ∧ (∀ a < root, out.mem a = mem a) ∧
      (∀ a, Rrep.foot root tok' a → root ≤ a ∧ a < finalHeap + 6 * newCap) ∧
      Rrep.phi root tok' out.mem = Rrep.phi root tok st.mem ∧ cost ≤ 102 * m + 17 * newCap + 240 := by
  dsimp only
  let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
  have hw15 : 15 < 2 ^ w := lt_of_lt_of_le (by decide : 15 < 2 ^ 14) (Nat.pow_le_pow_right (by decide) hw14)
  have hbelow : ∀ a, Rrep.foot root tok a → a < finalHeap := fun a ha => (hfoot a ha).2
  have htags := hrep.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hroot15W : root + 15 < 2 ^ w := by
    have hlt := hbelow (root + 15) (Or.inl (htags.1 _ (by rw [htags.2.1 15 (by omega)]; decide))); omega
  let s1 : State := { st with regs := Function.update st.regs 0 root }
  let s2 : State := { s1 with regs := Function.update s1.regs 5 tok.intCap }
  let s3 : State := { s2 with regs := Function.update s2.regs 8 finalHeap }
  have r1 : Runs w p ω (.assign 0 (.reg 8)) st .normal s1 2 :=
    runs_assign_iff.mpr ⟨root, by simp [Expr.eval, hr8], rfl, rfl, rfl⟩
  have r2 : Runs w p ω (.assign 5 (.load (.bin .add (.reg 0) (.const 15)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨tok.intCap, by
      simp [Expr.eval, BinOp.eval, s1, hw15, hroot15W, show st.mem (root + 15) = tok.intCap by simpa using hrep.1 15 (by simp)],
      rfl, rfl, rfl⟩
  have r3 : Runs w p ω (.assign 8 (.reg 9)) s2 .normal s3 2 :=
    runs_assign_iff.mpr ⟨finalHeap, by simp [Expr.eval, s2, s1, hr9], rfl, rfl, rfl⟩
  obtain ⟨cG, out, tok', hrG, hout14, hcapEq, htrEq, htrsEq, herCp, h18Eq, hrep', hpres', hphi',
      hz', hfr', hft', hcG⟩ :=
    growIntTablesFromReg7_runs (w := w) (L := L) (P := P) (m := m) (V := V) (psi := psi) (k := k)
      (epsExp := epsExp) (drainUnit := detectOffTreeDrainUnit L) (copyWords := copyWords)
      (root := root) (heap := finalHeap) (newCap := newCap) (st := s3) hlocal hCopy
      (by simp [s3, s2, s1]) (by simp [s3, s2]) (by simp [s3, s2, s1, hr7]) (by simp [s3])
      hrep hbelow hz (by omega) (by omega) (by omega) hw15 (by omega)
  have rRet : Runs w p ω (.ret (.reg 14)) out (.returned (finalHeap + 6 * newCap)) out 2 :=
    runs_ret_iff.mpr ⟨finalHeap + 6 * newCap, by simp [Expr.eval, hout14], rfl, rfl, rfl⟩
  have hrSeq : Runs w p ω
      (.assign 0 (.reg 8) ;; .assign 5 (.load (.bin .add (.reg 0) (.const 15))) ;;
       .assign 8 (.reg 9) ;; growIntTablesFromReg7 copyWords ;; .ret (.reg 14))
      st (.returned (finalHeap + 6 * newCap)) out (2 + (5 + (2 + (cG + 2 + 1) + 1) + 1) + 1) :=
    runs_seq_iff.mpr (Or.inr ⟨s1, 2, _, r1, runs_seq_iff.mpr (Or.inr ⟨s2, 5, _, r2,
      runs_seq_iff.mpr (Or.inr ⟨s3, 2, _, r3, runs_seq_iff.mpr (Or.inr ⟨out, cG, 2, hrG, rRet, rfl⟩), rfl⟩), rfl⟩), rfl⟩)
  have hrecAt (e : ℕ) (he : e ∈ s0.extG.E) (hnot : s0.extToInt e ∉ s0.chain.toTreeChain.chainTree.E)
      (val : PathEdgeValue) (hpa : PathEdgeAt out.mem (out.mem (tok'.edgeRecords + s0.extToInt e)) 4 L (some val)) :
      PathEdgeAt st.mem (st.mem (tok.edgeRecords + s0.extToInt e)) 4 L (some val) := by
    rw [herCp _ (htokCap.symm ▸ hExtInt e he)] at hpa
    exact hpa.congr fun x hlo hhi => by
      have ht18 : tok.tag x = 18 := by
        rw [← Nat.add_sub_of_le hlo]; exact (htags.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 e he).2 hnot _ (by omega)
      exact (h18Eq x (hbelow x (Or.inl (htags.1 x (by rw [ht18]; decide)))) ht18).symm
  refine ⟨_, out, tok', hrSeq, hrep', hcapEq, hpres', htrEq ▸ htrsEq ▸ hNum,
    ⟨fun e he hnot val hpa => hoffRec.1 e he hnot val (hrecAt e he hnot val hpa),
     fun e₁ he₁ e₂ he₂ hne hn₁ hn₂ => by
       rw [herCp _ (htokCap.symm ▸ hExtInt e₁ he₁), herCp _ (htokCap.symm ▸ hExtInt e₂ he₂)]
       exact hoffRec.2 e₁ he₁ e₂ he₂ hne hn₁ hn₂⟩,
    fun hgl e he hnot val hpa => hoffBound hgl e he hnot val (hrecAt e he hnot val hpa),
    by omega, by omega, hz',
    fun a ha => (hfr' a (by omega) (fun hf => by have := (hfoot a hf).1; omega)).trans (hcaller a ha),
    fun a ha => (hft' a ha).elim (fun h0 => ⟨(hfoot a h0).1, by have := (hfoot a h0).2; omega⟩)
      (fun ⟨h1, h2⟩ => ⟨by omega, h2⟩), hphi', by omega⟩

/-- Discharges `SolverInitStepSpecCredit` directly from `ordSolverInitWired_runs`. -/
theorem solverInitStepSpecCredit_of_wired {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m V psi k epsExp : ℕ) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (p : Program) (initProc initConcreteProc overwriteProc copyWords initSpace initFixed toolMul treeMul : ℕ)
    (hInitAt : p.procs[initProc]? = some (solverInitWiredBody initConcreteProc overwriteProc copyWords))
    (hFmt4 : F.fmt.limbBits = 4)
    (hRun : ∀ (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (∀ x ∈ args, x < 2 ^ w) → minRatioInitPreWithV F G m V (1 / (2 : ℝ) ^ k) cfg.α args mem →
      ZeroFrom mem (heapArg args) → heapArg args + initSpace < 2 ^ w →
      ∃ finalHeap cost out tok,
        let L := F.limbs; let P := F.fmt.precision
        let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
        let s0 := Chain.Ordered.algorithm2_init cfg G
          (readVector mem (args.getD 1 0) 4 L P m) (readVector mem (args.getD 2 0) 4 L P m)
        Runs w p ω (solverInitWiredBody initConcreteProc overwriteProc copyWords)
          (startState args mem pos) (.returned finalHeap) out cost ∧
        Rrep.rep (heapArg args) s0 tok out.mem ∧ tok.intCap = initTargetCap cfg G ∧
        SolverTreeNumericInv P s0 tok ∧ heapArg args ≤ finalHeap ∧ finalHeap ≤ heapArg args + initSpace ∧
        ZeroFrom out.mem finalHeap ∧ (∀ a < heapArg args, out.mem a = mem a) ∧
        (∀ a, Rrep.foot (heapArg args) tok a → heapArg args ≤ a ∧ a < finalHeap) ∧
        cost + Rrep.phi (heapArg args) tok out.mem ≤
          initFixed + toolMul * s0.chain.totalRuntime + treeMul * s0.chain.totalTreeUpdates) :
    SolverInitStepSpecCredit F cfg G m V psi k epsExp Rcore p initProc initSpace initFixed toolMul treeMul := by
  refine ⟨solverInitWiredBody initConcreteProc overwriteProc copyWords, hInitAt, fun args mem pos ω hargsW hpre hz hroom => ?_⟩
  obtain ⟨finalHeap, cost, out, tok, hr, hrep, hcap, hnum, hlo, hhi, hzOut, hframe, hfoot, hcost⟩ :=
    hRun args mem pos ω hargsW hpre hz hroom
  refine ⟨finalHeap, cost, out, tok, hr, ?_, ?_, hcap, ?_,
    ⟨hlo, hhi, hzOut, fun a ha _ => hframe a ha, fun a ha => Or.inr (hfoot a ha)⟩, ?_⟩
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using
      (algorithm2_init_stateFits (cfg := cfg) (G := G) (κ := 1 / (2 : ℝ) ^ k) (h := 4) (L := F.limbs) (P := F.fmt.precision))
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using hrep
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using hnum
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using hcost

/-- Discharges `SolverInitStepSpec` directly from `ordSolverInitWired_runs`. -/
theorem solverInitStepSpec_of_wired {w : ℕ} (F : MinRatioFormat w) (cfg : Alg2Config)
    (G : MGraph) (m V psi k epsExp : ℕ) (Rcore : DSRep (SparseCoreOrdAbs cfg.T))
    (p : Program) (initProc initConcreteProc overwriteProc copyWords initSpace initBudget : ℕ)
    (hInitAt : p.procs[initProc]? = some (solverInitWiredBody initConcreteProc overwriteProc copyWords))
    (hFmt4 : F.fmt.limbBits = 4)
    (hRun : ∀ (args : List ℕ) (mem : ℕ → ℕ) (pos : ℕ) (ω : ℕ → Bool),
      (∀ x ∈ args, x < 2 ^ w) → minRatioInitPreWithV F G m V (1 / (2 : ℝ) ^ k) cfg.α args mem →
      ZeroFrom mem (heapArg args) → heapArg args + initSpace < 2 ^ w →
      ∃ finalHeap cost out tok,
        let L := F.limbs; let P := F.fmt.precision
        let Rrep := solverStateRep cfg L P m V psi k epsExp (detectOffTreeDrainUnit L) Rcore
        let s0 := Chain.Ordered.algorithm2_init cfg G
          (readVector mem (args.getD 1 0) 4 L P m) (readVector mem (args.getD 2 0) 4 L P m)
        Runs w p ω (solverInitWiredBody initConcreteProc overwriteProc copyWords)
          (startState args mem pos) (.returned finalHeap) out cost ∧
        Rrep.rep (heapArg args) s0 tok out.mem ∧ tok.intCap = initTargetCap cfg G ∧
        SolverTreeNumericInv P s0 tok ∧ heapArg args ≤ finalHeap ∧ finalHeap ≤ heapArg args + initSpace ∧
        ZeroFrom out.mem finalHeap ∧ (∀ a < heapArg args, out.mem a = mem a) ∧
        (∀ a, Rrep.foot (heapArg args) tok a → heapArg args ≤ a ∧ a < finalHeap) ∧
        cost + Rrep.phi (heapArg args) tok out.mem ≤ initBudget) :
    SolverInitStepSpec F cfg G m V psi k epsExp Rcore p initProc initSpace initBudget := by
  refine ⟨solverInitWiredBody initConcreteProc overwriteProc copyWords, hInitAt, fun args mem pos ω hargsW hpre hz hroom => ?_⟩
  obtain ⟨finalHeap, cost, out, tok, hr, hrep, hcap, hnum, hlo, hhi, hzOut, hframe, hfoot, hcost⟩ :=
    hRun args mem pos ω hargsW hpre hz hroom
  refine ⟨finalHeap, cost, out, tok, hr, ?_, ?_, hcap, ?_,
    ⟨hlo, hhi, hzOut, fun a ha _ => hframe a ha, fun a ha => Or.inr (hfoot a ha)⟩, hcost⟩
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using
      (algorithm2_init_stateFits (cfg := cfg) (G := G) (κ := 1 / (2 : ℝ) ^ k) (h := 4) (L := F.limbs) (P := F.fmt.precision))
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using hrep
  · simpa only [hFmt4, Chain.Ordered.algorithm2_dsWithFailureWith, Chain.Ordered.algorithm2_dsWith] using hnum

end MinCostFlow.MinRatio
