module

public import MinCostFlow.MinRatio.RebuildLevel
public import MinCostFlow.MinRatio.ShiftForestScan
import MinCostFlow.MinRatio.RebuildModelSuffix

/-!
# Preparing the gradient of the next rebuilt level

Algorithm 1 (page 20) constructs the next core using the selected forest.
The traversal used after Shift also applies to the freshly initialized
branch zero in Rebuild.
-/

public section
namespace MinCostFlow.MinRatio
open WordRAM Chain DynSpanner.Program

/-- Compute the current graph's array addresses before Rebuild overwrites
its input graph register with the next graph. -/
@[expose] def prepareRebuildGraphArgs : Stmt :=
  .assign 18 (.load (.reg 6)) ;;
  .assign 50 (.load (.bin .add (.reg 6) (.const 1))) ;;
  .assign 17 (.bin .add (.bin .add (.reg 6) (.const 4)) (.bin .mul (.const 4) (.reg 18))) ;;
  .assign 15 (.bin .add (.bin .add (.bin .add (.reg 6) (.const 4))
    (.bin .mul (.const 7) (.reg 18))) (.bin .mul (.const 3) (.reg 50))) ;;
  .assign 16 (.bin .add (.reg 15) (.reg 50))

/-- The packed graph header and its allocation bound suffice to compute
the addresses, preserving all other inputs. -/
theorem prepareRebuildGraphArgs_runs {w a vc ec : ℕ} {G : MGraph}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (ha : st.regs 6 = a) (hG : DynGraphAt st.mem a vc ec G)
    (hroom : a + dynGraphSize vc ec < 2 ^ w) (hw : 7 < 2 ^ w) :
    ∃ out, Runs w p ω prepareRebuildGraphArgs st .normal out 36 ∧
      out.regs 50 = ec ∧ out.regs 17 = dgIntToExtBase a vc ∧
      out.regs 15 = dgETailSlotBase a vc ec ∧ out.regs 16 = dgEHeadSlotBase a vc ec ∧
      (∀ r, r ≠ 18 → r ≠ 50 → r ≠ 17 → r ≠ 15 → r ≠ 16 → out.regs r = st.regs r) ∧
      out.mem = st.mem := by
  simp only [dynGraphSize] at hroom
  have hv : st.mem a = vc := hG.2.2.2.1
  have he : st.mem (a + 1) = ec := hG.2.2.2.2.1
  have h₁ : 1 < 2 ^ w := by omega
  have h₃ : 3 < 2 ^ w := by omega
  have h₄ : 4 < 2 ^ w := by omega
  have ha₁ : a + 1 < 2 ^ w := by omega
  have ha₄ : a + 4 < 2 ^ w := by omega
  have hv₄ : 4 * vc < 2 ^ w := by omega
  have hv₇ : 7 * vc < 2 ^ w := by omega
  have he₃ : 3 * ec < 2 ^ w := by omega
  have hbase₄ : a + 4 + 4 * vc < 2 ^ w := by omega
  have hbase₇ : a + 4 + 7 * vc < 2 ^ w := by omega
  have htail : a + 4 + 7 * vc + 3 * ec < 2 ^ w := by omega
  have hhead : dgETailSlotBase a vc ec + ec < 2 ^ w := by
    unfold dgETailSlotBase
    omega
  let s1 := { st with regs := Function.update st.regs 18 vc }
  let s2 := { s1 with regs := Function.update s1.regs 50 ec }
  let s3 := { s2 with regs := Function.update s2.regs 17 (dgIntToExtBase a vc) }
  let s4 := { s3 with regs := Function.update s3.regs 15 (dgETailSlotBase a vc ec) }
  let s5 := { s4 with regs := Function.update s4.regs 16 (dgEHeadSlotBase a vc ec) }
  have hRun1 : Runs w p ω (.assign 18 (.load (.reg 6))) st .normal s1 3 :=
    runs_assign_iff.mpr ⟨vc, by simp [Expr.eval, ha, hv], rfl, rfl, rfl⟩
  have hRun2 : Runs w p ω (.assign 50 (.load (.bin .add (.reg 6) (.const 1)))) s1 .normal s2 5 :=
    runs_assign_iff.mpr ⟨ec, by
      simp [Expr.eval, BinOp.eval, s1, Function.update_of_ne, ha, h₁, ha₁, he], rfl, rfl, rfl⟩
  have hRun3 : Runs w p ω (.assign 17
      (.bin .add (.bin .add (.reg 6) (.const 4)) (.bin .mul (.const 4) (.reg 18)))) s2 .normal s3 8 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, s2, s1, Function.update_of_ne, ha, h₄, ha₄, hv₄, hbase₄,
        dgIntToExtBase], rfl, rfl, rfl⟩
  have hRun4 : Runs w p ω (.assign 15 (.bin .add (.bin .add (.bin .add (.reg 6) (.const 4))
      (.bin .mul (.const 7) (.reg 18))) (.bin .mul (.const 3) (.reg 50)))) s3 .normal s4 12 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, s3, s2, s1, Function.update_of_ne, ha, h₄, ha₄, hw, hv₇, he₃,
        h₃, hbase₇, htail, dgETailSlotBase], rfl, rfl, rfl⟩
  have hnext : dgETailSlotBase a vc ec + ec = dgEHeadSlotBase a vc ec := by
    unfold dgETailSlotBase dgEHeadSlotBase
    omega
  have hheadWord := hnext ▸ hhead
  have hRun5 : Runs w p ω (.assign 16 (.bin .add (.reg 15) (.reg 50))) s4 .normal s5 4 :=
    runs_assign_iff.mpr ⟨_, by
      simp [Expr.eval, BinOp.eval, s4, s3, s2, Function.update_of_ne, hheadWord, hnext],
      rfl, rfl, rfl⟩
  refine ⟨s5, ?_, ?_, ?_, ?_, ?_, ?_, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨s1, 3, 32, hRun1,
      runs_seq_iff.mpr (Or.inr ⟨s2, 5, 26, hRun2,
        runs_seq_iff.mpr (Or.inr ⟨s3, 8, 17, hRun3,
          runs_seq_iff.mpr (Or.inr ⟨s4, 12, 4, hRun4, hRun5, rfl⟩), rfl⟩), rfl⟩), by decide⟩)
  · simp [s5, s4, s3, s2, Function.update_of_ne]
  · simp [s5, s4, s3, Function.update_of_ne]
  · simp [s5, s4, Function.update_of_ne]
  · simp [s5]
  · intro r r18 r50 r17 r15 r16
    simp [s5, s4, s3, s2, s1, Function.update_of_ne, r18, r50, r17, r15, r16]

/-- Rebuild receives the current gradient in register 8. Copy its
pointer to register 13 before the traversal reuses register 8. -/
@[expose] def passRebuildGradient : Stmt :=
  .assign 13 (.reg 8)

/-- The gradient handoff changes just register 13 and costs two steps. -/
theorem passRebuildGradient_runs {w : ℕ} {p : Program} {st : State} {ω : ℕ → Bool} :
    ∃ out, Runs w p ω passRebuildGradient st .normal out 2 ∧
      out.regs 13 = st.regs 8 ∧ (∀ r ≠ 13, out.regs r = st.regs r) ∧
      out.mem = st.mem := by
  let out := { st with regs := Function.update st.regs 13 (st.regs 8) }
  have hr : Runs w p ω passRebuildGradient st .normal out 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  exact ⟨out, hr, by simp [out], fun r h => Function.update_of_ne h _ _, rfl⟩

/-- Read the new graph and lengths and compute the next gradient. -/
@[expose] def rebuildPrepareGradients (init read forestOp copy sort entry : ℕ) : Stmt :=
  rebuildReadForestLengths init read forestOp ;;
    passRebuildGradient ;; prepareShiftReadoutGradients copy sort entry

/-- The branch-zero readouts supply the graph and lengths for the shared
forest traversal. The output blocks fit below the returned free heap. -/
theorem rebuildPrepareGradients_runs
    {w copy sort entry a vc ec heap h limbs precision gradients base vcG ecG nextBase nextVC nextEC : ℕ} {G H : MGraph} {forest : LSF}
    {g : ℕ → ℝ} {init read forestOp prefixCost : ℕ} {p : Program} {initial st : State} {ω : ℕ → Bool}
    (hprefix : Runs w p ω (rebuildReadForestLengths init read forestOp)
      initial .normal st prefixCost)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hreadout : LSFAt st.mem (st.regs 9) vc ec h limbs precision G.E forest)
    (ha : st.mem (st.regs 9) = a)
    (hh : st.regs 5 = heap) (hlimbs : st.regs 67 = limbs) (hz : ZeroFrom st.mem heap)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap) (hlistEnd : dgVListBase a vc + forest.T.n ≤ heap)
    (hsortRoom : heap + forest.T.n + 2 < 2 ^ w) (hcount : 2 * forest.T.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : forest.T.IsForest)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision G.E g) (hsub : forest.T.E ⊆ G.E)
    (hgradEnd : ∀ e ∈ G.E, gradients + e * limbs + limbs ≤ heap)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hG : DynGraphAt st.mem base vcG ecG G) (hGEnd : base + dynGraphSize vcG ecG ≤ heap)
    (hvertices : G.V ⊆ forest.T.V)
    (hH : DynGraphAt st.mem nextBase nextVC nextEC H) (hHEnd : nextBase + dynGraphSize nextVC nextEC ≤ heap)
    (hHE : H.E ⊆ G.E) (h6 : st.regs 6 = nextBase)
    (h8 : st.regs 8 = gradients) (h50 : st.regs 50 = ecG)
    (h15 : st.regs 15 = dgETailSlotBase base vcG ecG)
    (h16 : st.regs 16 = dgEHeadSlotBase base vcG ecG)
    (h17 : st.regs 17 = dgIntToExtBase base vcG)
    (nextLengths : ℕ → ℝ)
    (hlen : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : st.regs 7 + nextEC * limbs ≤ heap) (hcapacity : nextEC ≤ ecG)
    (hwScan : 7 < 2 ^ w)
    (hspace : heap + forest.T.n + vc * limbs + limbs + vc + vc + 3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m < 2 ^ w)
    (hfit : let base := heap + forest.T.n
      let flags := base + vc * limbs + limbs
      let queue := flags + vc
      ∀ parent ∈ forest.T.V, ∀ e ∈ forest.T.E, ∀ direction : Bool, ∀ s seen r,
        ForestWorklistAt s forest.T g base flags queue vc h limbs precision r seen →
        EdgeValuesAt s.mem gradients h limbs precision G.E g →
        let value := Num.intVal s.mem (gradients + e * limbs) h limbs
        Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
          ((if direction then value else 0) - (if direction then 0 else value))))
    (hfitScan : ∀ mem,
      ForestPotentialsAt mem (heap + forest.T.n) h limbs precision forest.T g forest.T.V →
      EdgeValuesAt mem gradients h limbs precision G.E g →
      ∀ e ∈ G.E, Num.Fits h limbs
        (Num.intVal mem (gradients + e * limbs) h limbs +
          (Num.intVal mem (heap + forest.T.n + G.head e * limbs) h limbs -
            Num.intVal mem (heap + forest.T.n + G.tail e * limbs) h limbs))) :
    ∃ out cost, Runs w p ω (rebuildPrepareGradients init read forestOp copy sort entry)
        initial .normal out cost ∧
      out.regs 6 = nextBase ∧ out.regs 7 = st.regs 7 ∧
      heap ≤ out.regs 8 ∧ out.regs 8 + ecG * limbs ≤ out.regs 4 ∧
      DynGraphAt out.mem (out.regs 6) nextVC nextEC H ∧
      EdgeValuesAt out.mem (out.regs 7) h limbs precision H.E nextLengths ∧
      EdgeValuesAt out.mem (out.regs 8) h limbs precision H.E (Chain.coreGrad G forest g) ∧
      out.regs 6 + dynGraphSize nextVC nextEC ≤ out.regs 4 ∧
      out.regs 7 + nextEC * limbs ≤ out.regs 4 ∧
      out.regs 8 + nextEC * limbs ≤ out.regs 4 ∧
      ZeroFrom out.mem (out.regs 4) ∧
      heap ≤ out.regs 4 ∧
      out.regs 4 ≤ heap + forest.T.n + vc * limbs + limbs + vc + vc +
        3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m ∧
      (∀ addr < heap, out.mem addr = st.mem addr) ∧
      (∀ (σ : Type) (R : DSRep σ) (handle : ℕ) (model : σ) (x : R.τ),
        R.Local → R.rep handle model x st.mem →
        (∀ addr, R.foot handle x addr → addr < heap) →
        R.rep handle model x out.mem ∧ R.phi handle x out.mem = R.phi handle x st.mem) ∧
      cost ≤ 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m + 206 + prefixCost := by
  have hlenLive : ∀ e ∈ H.E, st.regs 7 + e * limbs + limbs ≤ heap := by
    intro e he
    have hcap : e < nextEC := hH.2.2.1 e he
    have hmul := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt hcap)
    rw [Nat.succ_mul] at hmul
    omega
  obtain ⟨ready, hpass, h13, hregs, hmem⟩ :=
    passRebuildGradient_runs (p := p) (ω := ω) (st := st)
  have h9 := hregs 9 (by decide)
  have h7 := hregs 7 (by decide)
  obtain ⟨out, c, hrun, ho6, ho7, ho8Lo, ho8, hg, hl, hgrad, hzero, hlo, hhi, hkeep, hc⟩ :=
    prepareShiftReadoutGradients_runs (ω := ω) (st := ready) hcopy hsort
      (by simpa only [hmem, h9] using hreadout) (by simpa only [hmem, h9] using ha)
      ((hregs 5 (by decide)).trans hh) ((hregs 67 (by decide)).trans hlimbs) (hmem.symm ▸ hz)
      hgraphEnd hlistEnd hsortRoom hcount hw hforest (hmem.symm ▸ hvalues) hsub hgradEnd
      himpl (hmem.symm ▸ hG) hGEnd hvertices (hmem.symm ▸ hH) hHEnd hHE
      ((hregs 6 (by decide)).trans h6) (h13.trans h8)
      ((hregs 50 (by decide)).trans h50) ((hregs 15 (by decide)).trans h15)
      ((hregs 16 (by decide)).trans h16) ((hregs 17 (by decide)).trans h17)
      nextLengths (by simpa only [hmem, h7] using hlen)
      (by simpa only [h7] using hlenLive) hwScan hspace hfit hfitScan
  have ho7 := ho7.trans h7
  have hframe (a : ℕ) (ha : a < heap) : out.mem a = st.mem a :=
    (hkeep a ha).trans (congrFun hmem a)
  refine ⟨out, prefixCost + c + 4,
    runs_seq_iff.mpr (Or.inr ⟨st, prefixCost, c + 3, hprefix,
      runs_seq_iff.mpr (Or.inr ⟨ready, 2, c, hpass, hrun, by omega⟩), by omega⟩),
    ho6, ho7, ho8Lo, ho8, hg, hl, hgrad, ho6.symm ▸ hHEnd.trans hlo, ho7.symm ▸ hlenEnd.trans hlo, ?_, hzero, hlo, hhi, hframe, ?_, by omega⟩
  · exact (Nat.add_le_add_left (Nat.mul_le_mul_right limbs hcapacity) _).trans ho8
  · intro σ R handle model x hlocal hrep hfoot
    have hk := hlocal handle model x st.mem out.mem (fun a ha => (hframe a (hfoot a ha)).symm)
    exact ⟨hk.1 hrep, hk.2.symm⟩

/-- The branch-zero traversal's gradient table represents the next
model level of periodic Rebuild (Algorithm 1, page 20). -/
theorem rebuildNextGradientAt
    {T : SparseCoreRestartTool} {last : LastLevelTool} {P : ChainParams}
    (chain : ChainState T P) (i : Fin P.d) (G : MGraph) (enc : ℕ)
    {mem : ℕ → ℕ} {table h limbs precision : ℕ} :
    let next := (algorithm1_rebuild T last P chain i.val G enc).1
    EdgeValuesAt mem table h limbs precision (next.G (i.val + 1)).E
      (coreGrad G (T.lsfs (next.scState i.val) 0) (chain.toTreeChain.chainGrad chain.g i.val)) →
    EdgeValuesAt mem table h limbs precision (next.G (i.val + 1)).E
      (next.toTreeChain.chainGrad chain.g (i.val + 1)) := by
  dsimp only
  rw [(rebuildNextLevelNumbers T last P chain i.val i.isLt G enc).2]
  exact id


/-- The suffix iteration can derive the traversal arguments from its
input graph while keeping the graph and all three input pointers. -/
theorem rebuildCoreGraphArgs_runs {w graph vCap eCap : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool} {G : MGraph}
    (hgraph : st.regs 6 = graph) (hG : DynGraphAt st.mem graph vCap eCap G)
    (hroom : graph + dynGraphSize vCap eCap < 2 ^ w) (hw : 7 < 2 ^ w) :
    ∃ args, Runs w p ω prepareRebuildGraphArgs
        { st with regs := Function.update (Function.update st.regs 53 (st.regs 19)) 54 (st.regs 21) }
        .normal args 36 ∧
      args.regs 50 = eCap ∧ args.regs 17 = dgIntToExtBase graph vCap ∧
      args.regs 15 = dgETailSlotBase graph vCap eCap ∧
      args.regs 16 = dgEHeadSlotBase graph vCap eCap ∧
      (∀ r, (r ≤ 8 ∨ r = 19 ∨ r = 21 ∨ r = 51 ∨ r = 52 ∨ 55 ≤ r) →
        args.regs r = st.regs r) ∧ args.mem = st.mem := by
  let saved := { st with regs := Function.update (Function.update st.regs 53 (st.regs 19)) 54 (st.regs 21) }
  have hsave (r : ℕ) (h53 : r ≠ 53) (h54 : r ≠ 54) : saved.regs r = st.regs r := by
    simp [saved, Function.update_of_ne, h53, h54]
  obtain ⟨args, hr, h50, h17, h15, h16, hregs, hmem⟩ :=
    prepareRebuildGraphArgs_runs (p := p) (ω := ω) (st := saved)
      ((hsave 6 (by decide) (by decide)).trans hgraph) hG hroom hw
  exact ⟨args, hr, h50, h17, h15, h16,
    fun r hr => (hregs r (by omega) (by omega) (by omega) (by omega) (by omega)).trans
      (hsave r (by omega) (by omega)), hmem⟩

/-- A sparse-core iteration of the Rebuild suffix keeps its level index
and terminal bound while the gradient scan uses those scratch registers. -/
@[expose] def rebuildPrepareGradientsIndexed (init read forestOp copy sort entry : ℕ) : Stmt :=
  .assign 53 (.reg 19) ;; .assign 54 (.reg 21) ;;
    prepareRebuildGraphArgs ;; rebuildPrepareGradients init read forestOp copy sort entry ;;
    .assign 19 (.reg 53) ;; .assign 21 (.reg 54)

/-- Set the graph arguments and save and restore the suffix registers in forty-nine steps, with
the graph and numerical table outputs of the gradient traversal intact. -/
theorem rebuildPrepareGradientsIndexed_runs
    {w init read forestOp copy sort entry cost : ℕ}
    {p : Program} {st args mid : State} {ω : ℕ → Bool}
    (hargs : Runs w p ω prepareRebuildGraphArgs
      { st with regs := Function.update (Function.update st.regs 53 (st.regs 19)) 54 (st.regs 21) }
      .normal args 36)
    (hbody : Runs w p ω (rebuildPrepareGradients init read forestOp copy sort entry)
      args .normal mid cost) :
    ∃ out, Runs w p ω (rebuildPrepareGradientsIndexed init read forestOp copy sort entry)
        st .normal out (cost + 49) ∧
      out.regs 19 = st.regs 19 ∧ out.regs 21 = st.regs 21 ∧
      (∀ r, r ≠ 19 → r ≠ 21 → out.regs r = mid.regs r) ∧ out.mem = mid.mem := by
  let first := { st with regs := Function.update st.regs 53 (st.regs 19) }
  let saved := { first with regs := Function.update first.regs 54 (st.regs 21) }
  have hsave₁ : Runs w p ω (.assign 53 (.reg 19)) st .normal first 2 :=
    runs_assign_iff.mpr ⟨_, rfl, rfl, rfl, rfl⟩
  have hsave₂ : Runs w p ω (.assign 54 (.reg 21)) first .normal saved 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, first, Function.update_of_ne], rfl, rfl, rfl⟩
  have hbound :
      writesBelow 53 (rebuildPrepareGradients init read forestOp copy sort entry) = true := rfl
  have hidx : mid.regs 53 = st.regs 19 :=
    (runs_preserves_above (by decide : 53 ≤ 53) hbound hbody).trans
      ((runs_preserves_above (s := prepareRebuildGraphArgs) (by decide : 53 ≤ 53) rfl hargs).trans
        (by simp [Function.update_of_ne]))
  have hlast : mid.regs 54 = st.regs 21 :=
    (runs_preserves_above (by decide : 53 ≤ 54) hbound hbody).trans
      ((runs_preserves_above (s := prepareRebuildGraphArgs) (by decide : 53 ≤ 54) rfl hargs).trans (by simp))
  let indexed := { mid with regs := Function.update mid.regs 19 (st.regs 19) }
  let out := { indexed with regs := Function.update indexed.regs 21 (st.regs 21) }
  have hrestore₁ : Runs w p ω (.assign 19 (.reg 53)) mid .normal indexed 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, hidx], rfl, rfl, rfl⟩
  have hrestore₂ : Runs w p ω (.assign 21 (.reg 54)) indexed .normal out 2 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, indexed, Function.update_of_ne, hlast],
      rfl, rfl, rfl⟩
  refine ⟨out, ?_, by simp [out, indexed, Function.update_of_ne], by simp [out], ?_, rfl⟩
  · exact runs_seq_iff.mpr (Or.inr ⟨first, 2, cost + 46, hsave₁,
      runs_seq_iff.mpr (Or.inr ⟨saved, 2, cost + 43, hsave₂,
        runs_seq_iff.mpr (Or.inr ⟨args, 36, cost + 6, hargs,
        runs_seq_iff.mpr (Or.inr ⟨mid, cost, 5, hbody,
          runs_seq_iff.mpr (Or.inr ⟨indexed, 2, 2, hrestore₁, hrestore₂, rfl⟩),
          by omega⟩), by omega⟩), by omega⟩), by omega⟩)
  · intro r h19 h21
    simp [out, indexed, Function.update_of_ne, h19, h21]

/-- The indexed body keeps the saved counter arguments in registers 55
and above. -/
theorem rebuildPrepareGradientsIndexed_writesBelow (init read forestOp copy sort entry : ℕ) :
    writesBelow 55 (rebuildPrepareGradientsIndexed init read forestOp copy sort entry) = true := rfl

/-- Advance the handle and branch table cursors to the next level of
Algorithm 1 Rebuild (page 20). -/
@[expose] def rebuildAdvanceDescriptors : Stmt :=
  .assign 51 (.bin .add (.reg 51) (.const 1)) ;;
    .assign 52 (.bin .add (.reg 52) (.const 1))

/-- The cursors move one word forward and leave the rebuilt data intact. -/
theorem rebuildAdvanceDescriptors_runs {w handleCell branchCell : ℕ}
    {p : Program} {st : State} {ω : ℕ → Bool}
    (hh : st.regs 51 = handleCell) (hb : st.regs 52 = branchCell)
    (hhRoom : handleCell + 1 < 2 ^ w) (hbRoom : branchCell + 1 < 2 ^ w) :
    ∃ out, Runs w p ω rebuildAdvanceDescriptors st .normal out 9 ∧
      out.regs 51 = handleCell + 1 ∧ out.regs 52 = branchCell + 1 ∧
      (∀ r, r ≠ 51 → r ≠ 52 → out.regs r = st.regs r) ∧ out.mem = st.mem := by
  have hw : 1 < 2 ^ w := by omega
  let mid := { st with regs := Function.update st.regs 51 (handleCell + 1) }
  let out := { mid with regs := Function.update mid.regs 52 (branchCell + 1) }
  have hfirst : Runs w p ω (.assign 51 (.bin .add (.reg 51) (.const 1))) st .normal mid 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, hh, hw, hhRoom], rfl, rfl, rfl⟩
  have hsecond : Runs w p ω (.assign 52 (.bin .add (.reg 52) (.const 1))) mid .normal out 4 :=
    runs_assign_iff.mpr ⟨_, by simp [Expr.eval, BinOp.eval, mid, Function.update_of_ne, hb, hw, hbRoom],
      rfl, rfl, rfl⟩
  refine ⟨out, runs_seq_iff.mpr (Or.inr ⟨mid, 4, 4, hfirst, hsecond, rfl⟩),
    by simp [out, mid, Function.update_of_ne], by simp [out], ?_, rfl⟩
  intro r h51 h52
  simp [out, mid, Function.update_of_ne, h51, h52]

/-- A Rebuild iteration installs a core, prepares the next level, and
advances the descriptor cursors. The enclosing loop advances the level. -/
@[expose] def rebuildCoreStep (init read forestOp copy sort entry : ℕ) : Stmt :=
  rebuildPrepareGradientsIndexed init read forestOp copy sort entry ;;
    rebuildAdvanceDescriptors

/-- The Rebuild iteration keeps the enclosing loop's saved counter arguments. -/
theorem rebuildCoreStep_writesBelow (init read forestOp copy sort entry : ℕ) :
    writesBelow 55 (rebuildCoreStep init read forestOp copy sort entry) = true := rfl

/-- The pointer advances and loop-register saves add 59 steps to a core
rebuild and its gradient propagation. The new input tables stay in place. -/
theorem rebuildCoreStep_runs
    {w init read forestOp copy sort entry cost handleCell branchCell : ℕ}
    {p : Program} {st args mid : State} {ω : ℕ → Bool}
    (hargs : Runs w p ω prepareRebuildGraphArgs
      { st with regs := Function.update (Function.update st.regs 53 (st.regs 19)) 54 (st.regs 21) }
      .normal args 36)
    (hbody : Runs w p ω (rebuildPrepareGradients init read forestOp copy sort entry)
      args .normal mid cost)
    (hh : st.regs 51 = handleCell) (hb : st.regs 52 = branchCell)
    (hhRoom : handleCell + 1 < 2 ^ w) (hbRoom : branchCell + 1 < 2 ^ w) :
    ∃ out, Runs w p ω (rebuildCoreStep init read forestOp copy sort entry)
        st .normal out (cost + 59) ∧
      out.regs 19 = st.regs 19 ∧ out.regs 21 = st.regs 21 ∧
      out.regs 51 = handleCell + 1 ∧ out.regs 52 = branchCell + 1 ∧
      (∀ r, r ≠ 19 → r ≠ 21 → r ≠ 51 → r ≠ 52 → out.regs r = mid.regs r) ∧
      out.mem = mid.mem := by
  have hwrites : writesBelow 51 (rebuildPrepareGradients init read forestOp copy sort entry) = true := rfl
  have hhMid : mid.regs 51 = handleCell :=
    (runs_preserves_above (by decide : 51 ≤ 51) hwrites hbody).trans
      ((runs_preserves_above (s := prepareRebuildGraphArgs) (by decide : 51 ≤ 51) rfl hargs).trans
        (by simpa using hh))
  have hbMid : mid.regs 52 = branchCell :=
    (runs_preserves_above (by decide : 51 ≤ 52) hwrites hbody).trans
      ((runs_preserves_above (s := prepareRebuildGraphArgs) (by decide : 51 ≤ 52) rfl hargs).trans
        (by simpa using hb))
  obtain ⟨ready, hr, h19, h21, hregs, hmem⟩ := rebuildPrepareGradientsIndexed_runs hargs hbody
  obtain ⟨out, ha, h51, h52, hregs', hmem'⟩ := rebuildAdvanceDescriptors_runs (ω := ω)
    ((hregs 51 (by decide) (by decide)).trans hhMid)
    ((hregs 52 (by decide) (by decide)).trans hbMid) hhRoom hbRoom
  exact ⟨out, runs_seq_iff.mpr (Or.inr ⟨ready, cost + 49, 9, hr, ha, by omega⟩),
    (hregs' 19 (by decide) (by decide)).trans h19,
    (hregs' 21 (by decide) (by decide)).trans h21, h51, h52,
    (fun r h19 h21 h51 h52 => (hregs' r h51 h52).trans (hregs r h19 h21)),
    hmem'.trans hmem⟩

/-- After advancing the descriptor cursors, the next graph and numerical
blocks constitute the next core's initializer input. The loop may now
increment its level without changing those inputs. -/
theorem rebuildCoreStep_nextInput_runs
    {w init read forestOp L copy sort entry cost handleCell branchCell k M N vc ec : ℕ}
    {fmt : Num.Format w} {tool : SparseCoreRestartTool} {G : MGraph}
    {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {p : Program} {st args mid : State} {ω : ℕ → Bool} {ℓ g : ℕ → ℝ}
    (hargs : Runs w p ω prepareRebuildGraphArgs
      { st with regs := Function.update (Function.update st.regs 53 (st.regs 19)) 54 (st.regs 21) }
      .normal args 36)
    (hbody : Runs w p ω (rebuildPrepareGradients init read forestOp copy sort entry)
      args .normal mid cost)
    (hh : st.regs 51 = handleCell) (hb : st.regs 52 = branchCell)
    (hhRoom : handleCell + 1 < 2 ^ w) (hbRoom : branchCell + 1 < 2 ^ w)
    (hk : 0 < k) (hm : G.m ≤ M) (hn : G.n ≤ N)
    (hgraph : DynGraphAt mid.mem (mid.regs 6) vc ec G)
    (hlen : EdgeValuesAt mid.mem (mid.regs 7) fmt.limbBits L fmt.precision G.E ℓ)
    (hgrad : EdgeValuesAt mid.mem (mid.regs 8) fmt.limbBits L fmt.precision G.E g)
    (hGRoom : mid.regs 6 + dynGraphSize vc ec ≤ mid.regs 4)
    (hLRoom : mid.regs 7 + ec * L ≤ mid.regs 4)
    (hgRoom : mid.regs 8 + ec * L ≤ mid.regs 4)
    (hpos : ∀ e ∈ G.E, 0 < ℓ e) (hz : ZeroFrom mid.mem (mid.regs 4)) :
    ∃ out, Runs w p ω (rebuildCoreStep init read forestOp copy sort entry)
        st .normal out (cost + 59) ∧
      out.regs 19 = st.regs 19 ∧ out.regs 21 = st.regs 21 ∧
      out.regs 51 = handleCell + 1 ∧ out.regs 52 = branchCell + 1 ∧
      (sparseCoreMachineContract fmt L tool G k M N vc ec costs allocation).initPre
        [out.regs 6, out.regs 7, out.regs 8, out.regs 4] out.mem ∧
      ZeroFrom out.mem (out.regs 4) := by
  obtain ⟨out, hr, hidx, hdepth, hhandle, hbranch, hregs, hmem⟩ :=
    rebuildCoreStep_runs hargs hbody hh hb hhRoom hbRoom
  have h6 := hregs 6 (by decide) (by decide) (by decide) (by decide)
  have h7 := hregs 7 (by decide) (by decide) (by decide) (by decide)
  have h8 := hregs 8 (by decide) (by decide) (by decide) (by decide)
  have h4 := hregs 4 (by decide) (by decide) (by decide) (by decide)
  refine ⟨out, hr, hidx, hdepth, hhandle, hbranch, ?_, ?_⟩
  · rw [hmem, h6, h7, h8, h4]
    exact sparseCoreMachineContract_initPre_of_tables hk hgraph hm hn hGRoom hLRoom hgRoom
      hlen hgrad hpos
  · simpa only [hmem, h4] using hz

/-- From the installed model core and its selected forest readout, the
traversal prepares the exact next model inputs while keeping the descriptor
and the core's potential (Algorithm 1, page 20). -/
theorem rebuildPrepareModelGradients_runs
    {w copy sort entry a vc ec heap h limbs precision gradients base vcG ecG nextBase nextVC nextEC handle handleCell branchCell : ℕ} {G H : MGraph} {forest : LSF}
    {g : ℕ → ℝ} {init read forestOp prefixCost : ℕ} {p : Program} {initial st : State} {ω : ℕ → Bool}
    {T : SparseCoreRestartTool} {P : ChainParams}
    (next : ChainState T P) (len grad : ℕ → ℝ) (i : Fin P.d)
    {R : DSRep T.State} {x : R.τ}
    (hprefix : Runs w p ω (rebuildReadForestLengths init read forestOp)
      initial .normal st prefixCost)
    (hcopy : MeetsContract w p copy (copyWordsContract w))
    (hsort : MeetsContract w p sort (Expander.heapSortContract w))
    (hreadout : LSFAt st.mem (st.regs 9) vc ec h limbs precision G.E forest)
    (ha : st.mem (st.regs 9) = a)
    (hh : st.regs 5 = heap) (hlimbs : st.regs 67 = limbs) (hz : ZeroFrom st.mem heap)
    (hgraphEnd : a + dynGraphSize vc ec ≤ heap)
    (hsortRoom : heap + forest.T.n + 2 < 2 ^ w) (hcount : 2 * forest.T.n + 2 < 2 ^ w)
    (hw : 4 ≤ 2 ^ w) (hforest : forest.T.IsForest)
    (hvalues : EdgeValuesAt st.mem gradients h limbs precision G.E g) (hsub : forest.T.E ⊆ G.E)
    (hgradTableEnd : gradients + ecG * limbs ≤ heap)
    (himpl : ∀ x y z, MeetsContract w p entry (writeCoreGradientCellContract w h x y z))
    (hG : DynGraphAt st.mem base vcG ecG G) (hGEnd : base + dynGraphSize vcG ecG ≤ heap)
    (hvertices : G.V ⊆ forest.T.V)
    (hH : DynGraphAt st.mem nextBase nextVC nextEC H) (hHEnd : nextBase + dynGraphSize nextVC nextEC ≤ heap)
    (hHE : H.E ⊆ G.E) (h6 : st.regs 6 = nextBase)
    (h8 : st.regs 8 = gradients) (h50 : st.regs 50 = ecG)
    (h15 : st.regs 15 = dgETailSlotBase base vcG ecG)
    (h16 : st.regs 16 = dgEHeadSlotBase base vcG ecG)
    (h17 : st.regs 17 = dgIntToExtBase base vcG)
    (nextLengths : ℕ → ℝ)
    (hlen : EdgeValuesAt st.mem (st.regs 7) h limbs precision H.E nextLengths)
    (hlenEnd : st.regs 7 + nextEC * limbs ≤ heap) (hcapacity : nextEC ≤ ecG)
    (hwScan : 7 < 2 ^ w)
    (hspace : heap + forest.T.n + vc * limbs + limbs + vc + vc + 3 * limbs * forest.T.vol forest.T.V + ecG * limbs + 3 * limbs * H.m < 2 ^ w)
    (hfit : let base := heap + forest.T.n
      let flags := base + vc * limbs + limbs
      let queue := flags + vc
      ∀ parent ∈ forest.T.V, ∀ e ∈ forest.T.E, ∀ direction : Bool, ∀ s seen r,
        ForestWorklistAt s forest.T g base flags queue vc h limbs precision r seen →
        EdgeValuesAt s.mem gradients h limbs precision G.E g →
        let value := Num.intVal s.mem (gradients + e * limbs) h limbs
        Num.Fits h limbs (Num.intVal s.mem (base + parent * limbs) h limbs +
          ((if direction then value else 0) - (if direction then 0 else value))))
    (hfitScan : ∀ mem,
      ForestPotentialsAt mem (heap + forest.T.n) h limbs precision forest.T g forest.T.V →
      EdgeValuesAt mem gradients h limbs precision G.E g →
      ∀ e ∈ G.E, Num.Fits h limbs
        (Num.intVal mem (gradients + e * limbs) h limbs +
          (Num.intVal mem (heap + forest.T.n + G.head e * limbs) h limbs -
            Num.intVal mem (heap + forest.T.n + G.tail e * limbs) h limbs))) :
    H = next.G (i.val + 1) →
    forest = T.lsfs (next.scState i.val) 0 →
    G = next.G i.val →
    g = next.toTreeChain.chainGrad grad i.val →
    nextLengths = next.toTreeChain.chainLen len (i.val + 1) →
    next.toTreeChain.chainGrad grad (i.val + 1) =
      coreGrad (next.G i.val) (T.lsfs (next.scState i.val) 0)
        (next.toTreeChain.chainGrad grad i.val) →
    R.Local → R.rep handle (next.scState i.val) x st.mem →
    (∀ addr, R.foot handle x addr → handle ≤ addr ∧ addr < heap) →
    st.mem handleCell = handle → st.mem branchCell = 0 →
    handleCell < heap → branchCell < heap → handle ≤ heap →
    (∀ addr < handle, addr ≠ handleCell → addr ≠ branchCell → st.mem addr = initial.mem addr) →
    ∃ out cost, Runs w p ω (rebuildPrepareGradients init read forestOp copy sort entry)
        initial .normal out cost ∧
      out.mem handleCell = handle ∧ out.mem branchCell = 0 ∧
      out.regs 6 = nextBase ∧ handle ≤ out.regs 8 ∧
      R.rep handle (next.scState i.val) x out.mem ∧
      R.phi handle x out.mem = R.phi handle x st.mem ∧
      DynGraphAt out.mem (out.regs 6) nextVC nextEC (next.G (i.val + 1)) ∧
      EdgeValuesAt out.mem (out.regs 7) h limbs precision (next.G (i.val + 1)).E
        (next.toTreeChain.chainLen len (i.val + 1)) ∧
      EdgeValuesAt out.mem (out.regs 8) h limbs precision (next.G (i.val + 1)).E
        (next.toTreeChain.chainGrad grad (i.val + 1)) ∧
      out.regs 6 + dynGraphSize nextVC nextEC ≤ out.regs 4 ∧
      out.regs 7 + nextEC * limbs ≤ out.regs 4 ∧
      out.regs 8 + nextEC * limbs ≤ out.regs 4 ∧
      ZeroFrom out.mem (out.regs 4) ∧
      handle ≤ out.regs 4 ∧
      (∀ addr, R.foot handle x addr → handle ≤ addr ∧ addr < out.regs 4) ∧
      (∀ addr < handle, addr ≠ handleCell → addr ≠ branchCell → out.mem addr = initial.mem addr) ∧
      cost ≤ 280 * (forest.T.n * (2 * Nat.log 2 (forest.T.n + 2) + 1) + 1) +
        forest.T.vol forest.T.V * (129 * limbs + 209) + 87 * forest.T.n +
        (129 * limbs + 172) * H.m + 206 + prefixCost := by
  intro hNext hForest hCurrent hGrad hLengths hnextGrad hlocal hrep hfoot hcell hbranch hhBelow hbBelow hhandleHeap hprefixFrame
  have hvertexBound : forest.T.n ≤ vc := by
    rw [← Finset.card_range vc]
    apply Finset.card_le_card
    intro v hv
    exact Finset.mem_range.mpr (hreadout.1.2.1 v hv)
  have hlistEnd : dgVListBase a vc + forest.T.n ≤ heap := by
    simp only [dgVListBase, dynGraphSize] at *
    omega
  have hgradEnd (edge : ℕ) (he : edge ∈ G.E) : gradients + edge * limbs + limbs ≤ heap := by
    have hcap := hG.2.2.1 edge he
    have hmul := Nat.mul_le_mul_right limbs (Nat.succ_le_of_lt hcap)
    rw [Nat.succ_mul] at hmul
    omega
  obtain ⟨out, c, hr, ho6, _, ho8Lo, _, hg, hl, hgrad, hgb, hlb, hgrb, hz', hLo, _, hframe, hkeep, hc⟩ :=
    rebuildPrepareGradients_runs hprefix hcopy hsort hreadout ha hh hlimbs hz
      hgraphEnd hlistEnd hsortRoom hcount hw hforest hvalues hsub hgradEnd himpl
      hG hGEnd hvertices hH hHEnd hHE h6 h8 h50 h15 h16 h17
      nextLengths hlen hlenEnd hcapacity hwScan hspace hfit hfitScan
  have hgrad' : EdgeValuesAt out.mem (out.regs 8) h limbs precision
      (next.G (i.val + 1)).E
      (next.toTreeChain.chainGrad grad (i.val + 1)) := by
    rw [hnextGrad]
    simpa only [hNext, hForest, hCurrent, hGrad] using hgrad
  obtain ⟨hrep', hphi⟩ := hkeep _ R handle _ x hlocal hrep (fun a ha => (hfoot a ha).2)
  exact ⟨out, c, hr, (hframe _ hhBelow).trans hcell, (hframe _ hbBelow).trans hbranch,
    ho6, hhandleHeap.trans ho8Lo,
    hrep', hphi, hNext ▸ hg, hNext ▸ (hLengths ▸ hl), hgrad', hgb, hlb, hgrb, hz',
    hhandleHeap.trans hLo, (fun a ha => ⟨(hfoot a ha).1, (hfoot a ha).2.trans_le hLo⟩),
    (fun a ha hd hb => (hframe a (ha.trans_le hhandleHeap)).trans (hprefixFrame a ha hd hb)), hc⟩

/-- The handle and branch tables of the already rebuilt levels.
Each live handle names a represented core whose footprint lies below
the free heap of the Rebuild suffix (Algorithm 1, page 20). -/
@[expose] def RebuiltCoresAt {T : SparseCoreRestartTool} {P : ChainParams}
    (R : DSRep T.State) (chain : ChainState T P) (mem : ℕ → ℕ)
    (handleBase branchBase first stop heap : ℕ) : Prop :=
  ∀ j, first ≤ j → j < stop →
    mem (branchBase + j) = chain.bran j ∧
    ∃ x : R.τ, R.rep (mem (handleBase + j)) (chain.scState j) x mem ∧
      handleBase + P.d < mem (handleBase + j) ∧ branchBase + P.d < mem (handleBase + j) ∧
      ∀ a, R.foot (mem (handleBase + j)) x a → mem (handleBase + j) ≤ a ∧ a < heap

/-- Extend the installed interval by one core. The step may change its
own two descriptor cells below the previous heap and allocate above it.
The earlier descriptors and their footprints are disjoint from those
two cells. -/
theorem RebuiltCoresAt.extend
    {T : SparseCoreRestartTool} {P : ChainParams} {R : DSRep T.State}
    {chain : ChainState T P} {mem mem' : ℕ → ℕ}
    {handleBase branchBase first stop heap heap' handle : ℕ} {x : R.τ}
    (hlocal : R.Local)
    (hprev : RebuiltCoresAt R chain mem handleBase branchBase first stop heap)
    (hfirst : first ≤ stop) (hheap : heap ≤ heap')
    (hstop : stop ≤ P.d)
    (hhEnd : handleBase + P.d < heap) (hbEnd : branchBase + P.d < heap)
    (htableSep : handleBase + stop < branchBase + first ∨ branchBase + stop < handleBase + first)
    (hframe : ∀ a < heap, a ≠ handleBase + stop → a ≠ branchBase + stop → mem' a = mem a)
    (hhandle : mem' (handleBase + stop) = handle)
    (hbranch : mem' (branchBase + stop) = chain.bran stop)
    (hrep : R.rep handle (chain.scState stop) x mem')
    (hhHandle : handleBase + P.d < handle) (hbHandle : branchBase + P.d < handle)
    (hfoot : ∀ a, R.foot handle x a → handle ≤ a ∧ a < heap') :
    RebuiltCoresAt R chain mem' handleBase branchBase first (stop + 1) heap' := by
  intro j hj hstop
  rcases eq_or_lt_of_le (Nat.le_of_lt_succ hstop) with rfl | hlt
  · exact ⟨hbranch, x, hhandle.symm ▸ hrep, hhandle.symm ▸ hhHandle, hhandle.symm ▸ hbHandle, hhandle.symm ▸ hfoot⟩
  · obtain ⟨hb, y, hy, hhLow, hbLow, hyFoot⟩ := hprev j hj hlt
    have hhKeep : mem' (handleBase + j) = mem (handleBase + j) :=
      hframe _ (by omega) (by omega) (by omega)
    have hbKeep : mem' (branchBase + j) = mem (branchBase + j) :=
      hframe _ (by omega) (by omega) (by omega)
    refine ⟨hbKeep.trans hb, y, ?_, hhKeep.symm ▸ hhLow, hhKeep.symm ▸ hbLow, ?_⟩
    · rw [hhKeep]
      apply (hlocal _ _ y mem mem' ?_).1 hy
      intro a ha
      obtain ⟨hlo, hhi⟩ := hyFoot a ha
      exact (hframe a hhi (by omega) (by omega)).symm
    · rw [hhKeep]
      exact fun a ha => ⟨(hyFoot a ha).1, (hyFoot a ha).2.trans_le hheap⟩

/-- A disjoint allocation and descriptor store leave the previously
installed cores represented beneath the advanced heap. -/
theorem RebuiltCoresAt.preserve
    {T : SparseCoreRestartTool} {P : ChainParams} {R : DSRep T.State}
    {chain : ChainState T P} {mem mem' : ℕ → ℕ}
    {handleBase branchBase first stop heap heap' handleCell branchCell : ℕ}
    (hin : RebuiltCoresAt R chain mem handleBase branchBase first stop heap)
    (hlocal : R.Local) (hheap : heap ≤ heap')
    (hh : handleBase + stop ≤ heap) (hb : branchBase + stop ≤ heap)
    (hsep : ∀ j, first ≤ j → j < stop →
      handleBase + j ≠ handleCell ∧ handleBase + j ≠ branchCell ∧
      branchBase + j ≠ handleCell ∧ branchBase + j ≠ branchCell)
    (hhWrite : handleCell ≤ handleBase + P.d ∨ handleCell ≤ branchBase + P.d)
    (hbWrite : branchCell ≤ handleBase + P.d ∨ branchCell ≤ branchBase + P.d)
    (hframe : ∀ a < heap, a ≠ handleCell → a ≠ branchCell → mem' a = mem a) :
    RebuiltCoresAt R chain mem' handleBase branchBase first stop heap' := by
  intro j hj hstop
  obtain ⟨hbranch, y, hrep, hhLow, hbLow, hfoot⟩ := hin j hj hstop
  obtain ⟨hha, hhb, hba, hbb⟩ := hsep j hj hstop
  have hhandle := hframe (handleBase + j) (by omega) hha hhb
  refine ⟨(hframe (branchBase + j) (by omega) hba hbb).trans hbranch, y, ?_, hhandle.symm ▸ hhLow, hhandle.symm ▸ hbLow, ?_⟩
  · rw [hhandle]
    apply (hlocal _ _ y mem mem' ?_).1 hrep
    intro a ha
    obtain ⟨hlo, hhi⟩ := hfoot a ha
    have hca : a ≠ handleCell := by rcases hhWrite with h | h <;> omega
    have hcb : a ≠ branchCell := by rcases hbWrite with h | h <;> omega
    exact (hframe a hhi hca hcb).symm
  · rw [hhandle]
    exact fun a ha => ⟨(hfoot a ha).1, (hfoot a ha).2.trans_le hheap⟩

/-- Before a suffix rebuild installs its first core, the installed
interval is empty. -/
theorem rebuiltCoresAt_empty
    {T : SparseCoreRestartTool} {P : ChainParams} (R : DSRep T.State)
    (chain : ChainState T P) (mem : ℕ → ℕ) (handleBase branchBase first heap : ℕ) :
    RebuiltCoresAt R chain mem handleBase branchBase first first heap := by
  intro j hj hlt
  exact False.elim ((Nat.not_lt_of_ge hj) hlt)

/-- The Rebuild body extends the installed interval while moving the
descriptor cursors. The enclosing loop can advance to the next level
with the extended interval unchanged. -/
theorem rebuildCoreStep_extend_runs
    {T : SparseCoreRestartTool} {P : ChainParams} {R : DSRep T.State}
    (chain : ChainState T P)
    {w init read forestOp copy sort entry cost first level heap handleBase branchBase : ℕ}
    {p : Program} {st args mid : State} {ω : ℕ → Bool} {x : R.τ}
    (hargs : Runs w p ω prepareRebuildGraphArgs
      { st with regs := Function.update (Function.update st.regs 53 (st.regs 19)) 54 (st.regs 21) }
      .normal args 36)
    (hbody : Runs w p ω (rebuildPrepareGradients init read forestOp copy sort entry)
      args .normal mid cost)
    (hindex : st.regs 19 = level)
    (hh : st.regs 51 = handleBase + level) (hb : st.regs 52 = branchBase + level)
    (hhRoom : handleBase + (level + 1) < 2 ^ w) (hbRoom : branchBase + (level + 1) < 2 ^ w)
    (hlocal : R.Local)
    (hprev : RebuiltCoresAt R chain st.mem handleBase branchBase first level heap)
    (hfirst : first ≤ level) (hheap : heap ≤ mid.regs 4)
    (hstop : level ≤ P.d)
    (hhEnd : handleBase + P.d < heap) (hbEnd : branchBase + P.d < heap)
    (htableSep : handleBase + level < branchBase + first ∨ branchBase + level < handleBase + first)
    (hframe : ∀ a < heap, a ≠ handleBase + level → a ≠ branchBase + level →
      mid.mem a = st.mem a)
    (hhandle : mid.mem (handleBase + level) = heap)
    (hbranch : mid.mem (branchBase + level) = chain.bran level)
    (hrep : R.rep heap (chain.scState level) x mid.mem)
    (hfoot : ∀ a, R.foot heap x a → heap ≤ a ∧ a < mid.regs 4) :
    ∃ out, Runs w p ω (rebuildCoreStep init read forestOp copy sort entry)
        st .normal out (cost + 59) ∧
      out.regs 19 = level ∧ out.regs 21 = st.regs 21 ∧
      out.regs 51 = handleBase + (level + 1) ∧ out.regs 52 = branchBase + (level + 1) ∧
      RebuiltCoresAt R chain out.mem handleBase branchBase first (level + 1) (out.regs 4) ∧
      (∀ r, r ≠ 19 → r ≠ 21 → r ≠ 51 → r ≠ 52 → out.regs r = mid.regs r) ∧
      out.mem = mid.mem := by
  obtain ⟨out, hr, hidx, hdepth, hhout, hbout, hregs, hmem⟩ :=
    rebuildCoreStep_runs hargs hbody hh hb (by omega) (by omega)
  have h4 := hregs 4 (by decide) (by decide) (by decide) (by decide)
  have hnext := RebuiltCoresAt.extend hlocal hprev hfirst hheap hstop hhEnd hbEnd htableSep hframe
    hhandle hbranch hrep hhEnd hbEnd hfoot
  exact ⟨out, hr, hidx.trans hindex, hdepth, by omega, by omega,
    by simpa only [hmem, h4] using hnext, hregs, hmem⟩

/-- At the head of the suffix loop, the installed interval stops at
the current level. The input registers point to that level's graph,
lengths and gradients below the free heap (Algorithm 1, page 20). -/
structure RebuildSuffixAt {T : SparseCoreRestartTool} {P : ChainParams}
    (R : DSRep T.State) (chain : ChainState T P) (len grad : ℕ → ℝ)
    (handleBase branchBase first level vc ec h limbs precision : ℕ) (st : State) : Prop where
  index : st.regs 19 = level
  depth : st.regs 21 = P.d
  handleCursor : st.regs 51 = handleBase + level
  branchCursor : st.regs 52 = branchBase + level
  installed : RebuiltCoresAt R chain st.mem handleBase branchBase first level (st.regs 4)
  graph : DynGraphAt st.mem (st.regs 6) vc ec (chain.G level)
  lengths : EdgeValuesAt st.mem (st.regs 7) h limbs precision (chain.G level).E
    (chain.toTreeChain.chainLen len level)
  gradients : EdgeValuesAt st.mem (st.regs 8) h limbs precision (chain.G level).E
    (chain.toTreeChain.chainGrad grad level)
  graphEnd : st.regs 6 + dynGraphSize vc ec ≤ st.regs 4
  lengthsEnd : st.regs 7 + ec * limbs ≤ st.regs 4
  gradientsEnd : st.regs 8 + ec * limbs ≤ st.regs 4
  free : ZeroFrom st.mem (st.regs 4)

/-- An Init allocation below both descriptor tables survives a rebuild
step whose stores below the live heap are confined to the two descriptors. -/
theorem RebuildSuffixAt.preserve_init_memory
    {T : SparseCoreRestartTool} {P : ChainParams} {R : DSRep T.State}
    {chain : ChainState T P} {len grad : ℕ → ℝ}
    {handleBase branchBase first level vc ec h limbs precision base : ℕ}
    {st out : State}
    (hin : RebuildSuffixAt R chain len grad handleBase branchBase first level vc ec h limbs precision st)
    (hhandle : base ≤ handleBase) (hbranch : base ≤ branchBase)
    (hheap : base ≤ st.regs 4)
    (hframe : ∀ a < st.regs 4, a ≠ st.regs 51 → a ≠ st.regs 52 → out.mem a = st.mem a) :
    ∀ a < base, out.mem a = st.mem a := by
  intro a ha
  apply hframe a (ha.trans_le hheap)
  · rw [hin.handleCursor]
    exact Nat.ne_of_lt (ha.trans_le (hhandle.trans (Nat.le_add_right _ _)))
  · rw [hin.branchCursor]
    exact Nat.ne_of_lt (ha.trans_le (hbranch.trans (Nat.le_add_right _ _)))

/-- Compute the traversal addresses from the suffix invariant and
retain the input it gives to the level initializer. -/
theorem RebuildSuffixAt.prepareGraphArgs_runs
    {T : SparseCoreRestartTool} {P : ChainParams} {R : DSRep T.State}
    {chain : ChainState T P} {len grad : ℕ → ℝ}
    {w handleBase branchBase first level vc ec h limbs precision : ℕ} {st : State}
    {p : Program} {ω : ℕ → Bool}
    (hin : RebuildSuffixAt R chain len grad handleBase branchBase first level vc ec h limbs precision st)
    (hheap : st.regs 4 < 2 ^ w) (hw : 7 < 2 ^ w) :
    ∃ args, Runs w p ω prepareRebuildGraphArgs
        { st with regs := Function.update (Function.update st.regs 53 (st.regs 19)) 54 (st.regs 21) }
        .normal args 36 ∧
      args.regs 50 = ec ∧ args.regs 17 = dgIntToExtBase (st.regs 6) vc ∧
      args.regs 15 = dgETailSlotBase (st.regs 6) vc ec ∧
      args.regs 16 = dgEHeadSlotBase (st.regs 6) vc ec ∧
      RebuildSuffixAt R chain len grad handleBase branchBase first level vc ec h limbs precision args ∧
      (∀ r, (r ≤ 8 ∨ r = 19 ∨ r = 21 ∨ r = 51 ∨ r = 52 ∨ 55 ≤ r) →
        args.regs r = st.regs r) ∧ args.mem = st.mem := by
  obtain ⟨args, hr, h50, h17, h15, h16, hregs, hmem⟩ :=
    rebuildCoreGraphArgs_runs (ω := ω) rfl hin.graph (hin.graphEnd.trans_lt hheap) hw
  have h4 := hregs 4 (by decide)
  have h6 := hregs 6 (by decide)
  have h7 := hregs 7 (by decide)
  have h8 := hregs 8 (by decide)
  refine ⟨args, hr, h50, h17, h15, h16, ?_, hregs, hmem⟩
  exact ⟨(hregs 19 (by decide)).trans hin.index, (hregs 21 (by decide)).trans hin.depth,
    (hregs 51 (by decide)).trans hin.handleCursor, (hregs 52 (by decide)).trans hin.branchCursor,
    by simpa only [hmem, h4] using hin.installed,
    by simpa only [hmem, h6] using hin.graph,
    by simpa only [hmem, h7] using hin.lengths,
    by simpa only [hmem, h8] using hin.gradients,
    by simpa only [h6, h4] using hin.graphEnd,
    by simpa only [h7, h4] using hin.lengthsEnd,
    by simpa only [h8, h4] using hin.gradientsEnd,
    by simpa only [hmem, h4] using hin.free⟩

/-- Install the modeled core of a periodic Rebuild iteration directly
from the loop-head tables and descriptor cursors. -/
theorem RebuildSuffixAt.installCore_runs
    {T : SparseCoreRestartTool} {P : ChainParams} {tool : LastLevelTool} {R : DSRep T.State}
    (chain : ChainState T P) (Gnew : MGraph) (enc : ℕ)
    {w init handleBase branchBase first level vc ec M N limbs : ℕ} {st : State}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {p : Program} {ω : ℕ → Bool} {op : ℕ → ℕ}
    :
    let next := (algorithm1_rebuild T tool P chain first Gnew enc).1
    let len := next.toTreeChain.chainLen chain.ℓ level
    let grad := next.toTreeChain.chainGrad chain.g level
    RebuildSuffixAt R next chain.ℓ chain.g handleBase branchBase first level vc ec
      fmt.limbBits limbs fmt.precision st →
    R.Implements w p init op
      (sparseCoreMachineContract fmt limbs T (next.G level) P.k M N vc ec costs allocation) →
    (next.G level).m ≤ M → (next.G level).n ≤ N →
    (∀ e ∈ (next.G level).E, 0 < len e) →
    next.scState level = T.init P.k M N (next.G level)
      (fun e => if e ∈ (next.G level).E then len e else 0)
      (fun e => if e ∈ (next.G level).E then grad e else 0) →
    st.regs 4 + allocation 5 [st.regs 6, st.regs 7, st.regs 8, st.regs 4] < 2 ^ w →
    handleBase + level ≠ branchBase + level →
    handleBase + level < st.regs 4 → branchBase + level < st.regs 4 →
    ∃ out ret cost y,
      Runs w p ω (rebuildInstallLevel init) st .normal out cost ∧
      out.mem (handleBase + level) = st.regs 4 ∧
      out.mem (branchBase + level) = 0 ∧ out.regs 4 = ret ∧
      R.rep (st.regs 4) (next.scState level) y out.mem ∧ ZeroFrom out.mem ret ∧
      SparseCoreInput T.toSparseCoreTool T.restart P.k (next.scState level) (next.G level) ∧
      out.regs 2 = 0 ∧ out.regs 3 = st.regs 4 ∧
      st.regs 4 ≤ ret ∧ ret ≤ st.regs 4 + allocation 5 [st.regs 6, st.regs 7, st.regs 8, st.regs 4] ∧
      (∀ a, R.foot (st.regs 4) y a → st.regs 4 ≤ a ∧ a < ret) ∧
      (∀ a < st.regs 4, a ≠ handleBase + level → a ≠ branchBase + level → out.mem a = st.mem a) ∧
      cost + R.phi (st.regs 4) y out.mem ≤ costs.factor M N * (M + 1) * P.k + 19 := by
  dsimp only
  intro hin himpl hm hn hpos hmodel hroom hne hh hb
  exact rebuildInstallCore_runs (ω := ω) _ _ hmodel himpl rfl rfl rfl rfl hin.graph hm hn
    hin.graphEnd hin.lengthsEnd hin.gradientsEnd hin.lengths hin.gradients hpos hin.free
    hroom hin.handleCursor hin.branchCursor hne hh hb

/-- Prepare the selected forest and the exact next lengths starting from
a periodic Rebuild loop head (Algorithm 1, page 20). -/
theorem RebuildSuffixAt.readCoreLengths_runs
    {T : SparseCoreRestartTool} {P : ChainParams} {tool : LastLevelTool} {R : DSRep T.State}
    (chain : ChainState T P) (Gnew : MGraph) (enc : ℕ)
    {w init handleBase branchBase first level vc ec M N limbs : ℕ} {st : State}
    {fmt : Num.Format w} {costs : SparseCoreMachineCosts} {allocation : ℕ → List ℕ → ℕ}
    {p : Program} {ω : ℕ → Bool} {op : ℕ → ℕ}
    (hfirst : first ≤ level) (hlevel : level < P.d) :
    let next := (algorithm1_rebuild T tool P chain first Gnew enc).1
    let G := next.G level
    let H := next.G (level + 1)
    let len := next.toTreeChain.chainLen chain.ℓ level
    let grad := next.toTreeChain.chainGrad chain.g level
    let forest := T.lsfs (next.scState level) 0
    let hc := handleBase + level
    let bc := branchBase + level
    RebuildSuffixAt R next chain.ℓ chain.g handleBase branchBase first level vc ec
      fmt.limbBits limbs fmt.precision st →
    R.Implements w p init op
      (sparseCoreMachineContract fmt limbs T G P.k M N vc ec costs allocation) →
    G.m ≤ M → G.n ≤ N →
    (∀ e ∈ G.E, 0 < len e) →
    next.scState level = T.init P.k M N G
      (fun e => if e ∈ G.E then len e else 0)
      (fun e => if e ∈ G.E then grad e else 0) →
    st.regs 4 + allocation 5 [st.regs 6, st.regs 7, st.regs 8, st.regs 4] + 1 < 2 ^ w →
    P.k < 2 ^ w → 9 < 2 ^ w →
    hc ≠ bc → hc < st.regs 4 → bc < st.regs 4 →
    (∀ mid top v e cost,
      Runs w p ω (rebuildInstallReadGraph init (op 3)) st .normal mid cost →
      mid.regs 5 = top → DynGraphAt mid.mem (mid.regs 6) v e H →
      mid.regs 6 + dynGraphSize v e ≤ top ∧ top + dynGraphSize v e + 4 < 2 ^ w) →
    (∀ a, st.regs 6 ≤ a → a < st.regs 6 + dynGraphSize vc ec → a ≠ hc ∧ a ≠ bc) →
    (∀ e ∈ G.E, ∀ j < limbs, st.regs 8 + e * limbs + j ≠ hc ∧ st.regs 8 + e * limbs + j ≠ bc) →
    H.E ⊆ G.E →
    (∀ mid c fv fe,
      Runs w p ω (rebuildReadForest init (op 3) (op 2)) st .normal mid c →
      LSFAt mid.mem (mid.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest →
      EdgeValuesAt mid.mem (mid.mem (mid.mem (mid.regs 9 + 3) + 1))
        fmt.limbBits limbs fmt.precision G.E len) →
    ∃ out v e cost y,
      Runs w p ω (rebuildReadForestLengths init (op 3) (op 2)) st .normal out cost ∧
      out.mem hc = st.regs 4 ∧ out.mem bc = 0 ∧
      R.rep (st.regs 4) (next.scState level) y out.mem ∧
      DynGraphAt out.mem (out.regs 6) v e H ∧
      EdgeValuesAt out.mem (out.regs 7) fmt.limbBits limbs fmt.precision H.E
        (next.toTreeChain.chainLen chain.ℓ (level + 1)) ∧
      out.regs 6 + dynGraphSize v e ≤ out.regs 5 ∧
      st.regs 4 ≤ out.regs 6 ∧ st.regs 4 ≤ out.regs 5 ∧ ZeroFrom out.mem (out.regs 5) ∧
      (∃ fv fe, LSFAt out.mem (out.regs 9) fv fe fmt.limbBits limbs fmt.precision G.E forest) ∧
      (∀ a < st.regs 4, a ≠ hc → a ≠ bc → out.mem a = st.mem a) ∧
      (∀ a, R.foot (st.regs 4) y a → st.regs 4 ≤ a ∧ a < out.regs 5) ∧
      DynGraphAt out.mem (st.regs 6) vc ec G ∧
      st.regs 6 + dynGraphSize vc ec ≤ out.regs 5 ∧
      st.regs 8 + ec * limbs ≤ out.regs 5 ∧
      EdgeValuesAt out.mem (st.regs 8) fmt.limbBits limbs fmt.precision G.E grad ∧
      (∀ r, r = 8 ∨ 13 ≤ r → out.regs r = st.regs r) ∧
      cost + R.phi (st.regs 4) y out.mem ≤ costs.factor M N * (M + 1) * P.k + 17 * dynGraphSize v e + 219 := by
  dsimp only
  intro hin himpl hm hn hpos hmodel hroom hk hw hne hh hb hcopy hgraphSep hgradSep hsub hden
  obtain ⟨_, hnext⟩ := algorithm1_rebuild_coreAt T tool P chain first level hfirst hlevel Gnew enc
  have hnextLen := (rebuildSuffix_nextLevelNumbers T tool P chain first level hfirst hlevel Gnew enc).1
  obtain ⟨out, copied, v, e, cost, y, hrun, hhandle, hbranch, hptr, hG, hrep, hℓ, hcopyEnd, hcopiedLo, hheap,
      hfree, hforest, hframe, hfoot, hbase, hg, hregs, hcost⟩ :=
    rebuildCore_lengths_runs (ω := ω) _ _ hmodel hnext _ hnextLen himpl rfl rfl rfl rfl
      hin.graph hm hn hin.graphEnd hin.lengthsEnd hin.gradientsEnd hin.lengths hin.gradients
      hpos hin.free hroom hk hin.handleCursor hin.branchCursor hne hh hb hw
      hcopy hgraphSep hsub hden
  exact ⟨out, v, e, cost, y, hrun, hhandle, hbranch, hrep, hptr.symm ▸ hG, hℓ, hptr.symm ▸ hcopyEnd, hptr.symm ▸ hcopiedLo, hheap,
    hfree, hforest, hframe, hfoot, hbase, hin.graphEnd.trans hheap, hin.gradientsEnd.trans hheap, hg hgradSep, hregs, hcost⟩

/-- After the core body installs a level and prepares the next input,
the loop index increment reestablishes the suffix invariant. -/
theorem RebuildSuffixAt.advance
    {T : SparseCoreRestartTool} {P : ChainParams} {R : DSRep T.State}
    {chain : ChainState T P} {len grad : ℕ → ℝ}
    {handleBase branchBase first level vc ec h limbs precision : ℕ} {mid out : State}
    (hdepth : out.regs 21 = P.d)
    (hh : out.regs 51 = handleBase + (level + 1))
    (hb : out.regs 52 = branchBase + (level + 1))
    (hinstalled : RebuiltCoresAt R chain out.mem handleBase branchBase first (level + 1) (out.regs 4))
    (hmem : out.mem = mid.mem)
    (hregs : ∀ r, r ≠ 19 → r ≠ 21 → r ≠ 51 → r ≠ 52 → out.regs r = mid.regs r)
    (hg : DynGraphAt mid.mem (mid.regs 6) vc ec (chain.G (level + 1)))
    (hl : EdgeValuesAt mid.mem (mid.regs 7) h limbs precision (chain.G (level + 1)).E
      (chain.toTreeChain.chainLen len (level + 1)))
    (hn : EdgeValuesAt mid.mem (mid.regs 8) h limbs precision (chain.G (level + 1)).E
      (chain.toTreeChain.chainGrad grad (level + 1)))
    (hgEnd : mid.regs 6 + dynGraphSize vc ec ≤ mid.regs 4)
    (hlEnd : mid.regs 7 + ec * limbs ≤ mid.regs 4)
    (hnEnd : mid.regs 8 + ec * limbs ≤ mid.regs 4)
    (hfree : ZeroFrom mid.mem (mid.regs 4)) :
    RebuildSuffixAt R chain len grad handleBase branchBase first (level + 1) vc ec h limbs precision
      { out with regs := Function.update out.regs 19 (level + 1) } := by
  have h4 := hregs 4 (by decide) (by decide) (by decide) (by decide)
  have h6 := hregs 6 (by decide) (by decide) (by decide) (by decide)
  have h7 := hregs 7 (by decide) (by decide) (by decide) (by decide)
  have h8 := hregs 8 (by decide) (by decide) (by decide) (by decide)
  constructor <;> dsimp only <;> simp (config := { decide := true }) only
    [Function.update_self, Function.update_of_ne, ne_eq,
      hdepth, hh, hb, hmem, h4, h6, h7, h8] at *
  all_goals assumption

/-- The core body and index increment carry the exact suffix invariant
to the next level, given the prepared model tables and the core allocation
frame (Algorithm 1, page 20). -/
theorem rebuildCoreStep_suffixAt_runs
    {T : SparseCoreRestartTool} {P : ChainParams} {R : DSRep T.State}
    (chain : ChainState T P) (len grad : ℕ → ℝ)
    {vc ec nextVC nextEC h precision : ℕ}
    {w init read forestOp limbs copy sort entry cost first level heap handleBase branchBase : ℕ}
    {p : Program} {st args mid : State} {ω : ℕ → Bool} {x : R.τ}
    (hargs : Runs w p ω prepareRebuildGraphArgs
      { st with regs := Function.update (Function.update st.regs 53 (st.regs 19)) 54 (st.regs 21) }
      .normal args 36)
    (hbody : Runs w p ω (rebuildPrepareGradients init read forestOp copy sort entry)
      args .normal mid cost)
    (hin : RebuildSuffixAt R chain len grad handleBase branchBase first level vc ec h limbs precision st)
    (hword : heap < 2 ^ w)
    (hlocal : R.Local)
    (hheapEntry : st.regs 4 = heap)
    (hfirst : first ≤ level) (hheap : heap ≤ mid.regs 4)
    (hstop : level < P.d)
    (hhEnd : handleBase + P.d < heap) (hbEnd : branchBase + P.d < heap)
    (htableSep : handleBase + P.d < branchBase + first ∨ branchBase + P.d < handleBase + first)
    (hframe : ∀ a < heap, a ≠ handleBase + level → a ≠ branchBase + level →
      mid.mem a = st.mem a)
    (hhandle : mid.mem (handleBase + level) = heap)
    (hbranch : mid.mem (branchBase + level) = chain.bran level)
    (hrep : R.rep heap (chain.scState level) x mid.mem)
    (hfoot : ∀ a, R.foot heap x a → heap ≤ a ∧ a < mid.regs 4)
    (hg : DynGraphAt mid.mem (mid.regs 6) nextVC nextEC (chain.G (level + 1)))
    (hl : EdgeValuesAt mid.mem (mid.regs 7) h limbs precision (chain.G (level + 1)).E
      (chain.toTreeChain.chainLen len (level + 1)))
    (hn : EdgeValuesAt mid.mem (mid.regs 8) h limbs precision (chain.G (level + 1)).E
      (chain.toTreeChain.chainGrad grad (level + 1)))
    (hgEnd : mid.regs 6 + dynGraphSize nextVC nextEC ≤ mid.regs 4)
    (hlEnd : mid.regs 7 + nextEC * limbs ≤ mid.regs 4)
    (hnEnd : mid.regs 8 + nextEC * limbs ≤ mid.regs 4)
    (hfree : ZeroFrom mid.mem (mid.regs 4)) :
    ∃ out, Runs w p ω (rebuildCoreStep init read forestOp copy sort entry)
        st .normal out (cost + 59) ∧
      RebuildSuffixAt R chain len grad handleBase branchBase first (level + 1) nextVC nextEC h limbs precision
        { out with regs := Function.update out.regs 19 (level + 1) } ∧
      out.regs 19 = level ∧ out.regs 6 = mid.regs 6 ∧ out.regs 8 = mid.regs 8 ∧
      out.mem = mid.mem ∧ heap ≤ out.regs 4 := by
  have hsep : handleBase + level < branchBase + first ∨ branchBase + level < handleBase + first :=
    htableSep.imp (by omega) (by omega)
  have hprev := hheapEntry ▸ hin.installed
  obtain ⟨out, hr, hi, hd, hh, hb, hinstalled, hregs, hmem⟩ :=
    rebuildCoreStep_extend_runs chain hargs hbody hin.index hin.handleCursor hin.branchCursor
      (by omega) (by omega) hlocal hprev hfirst hheap hstop.le hhEnd hbEnd hsep hframe
      hhandle hbranch hrep hfoot
  refine ⟨out, hr, RebuildSuffixAt.advance (hd.trans hin.depth) hh hb hinstalled hmem hregs
    hg hl hn hgEnd hlEnd hnEnd hfree, hi,
    hregs 6 (by decide) (by decide) (by decide) (by decide),
    hregs 8 (by decide) (by decide) (by decide) (by decide), hmem, ?_⟩
  rw [hregs 4 (by decide) (by decide) (by decide) (by decide)]
  exact hheap

end MinCostFlow.MinRatio
