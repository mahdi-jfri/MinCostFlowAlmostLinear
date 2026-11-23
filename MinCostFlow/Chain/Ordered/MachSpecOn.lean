module

public import MinCostFlow.Chain.Ordered.SpecOn
public import MinCostFlow.Chain.BundleRestartMachSpec

/-!
# The restricted specification of the machine-cost bundle tool

`sparseCoreBundleRestartToolMachWith_isSpecOrdRestartOn` is the restricted form
(`IsSpecOrdRestartOn`) of `sparseCoreBundleRestartToolMachWith_isSpecOrdRestart`
(`Chain/BundleRestartMachSpec.lean`, Lemma 5.17, pages 23–24): the per-instance hypotheses
`BundleCoreHypsAtWith` are asked only on the instances that satisfy a predicate `Pred`.

The proof is that of the unrestricted form. The machine-cost tool has the same runs as
`sparseCoreBundleRestartToolWith`, so the non-cost items come from `bundleRestartWith_spec`, the
restart cost from `bundleRestartMachWith_restartCost`, and the total cost from
`bundleRestartMachWith_totalCost_le`. The file also gives `ToolNoReinsertOrdRestart` for the
machine-cost tool, which is about runs only.
-/

@[expose] public section

namespace MinCostFlow.Chain.Ordered

open MinCostFlow MinCostFlow.LSF MinCostFlow.SparseCore MinCostFlow.DynSpanner MinCostFlow.Bundle

/-- **Restricted `IsSpecOrdRestartOn` for the machine cost** (Lemma 5.17, pages 23–24).
`sparseCoreBundleRestartToolMachWith lsfInit` meets the specification with
`bundleCoreParamsMachWith E spanConst` on every instance that satisfies `Pred`, given
`BundleCoreHypsAtWith` and `SparsifyParamsLe (params M) (E.P_fn M)` on those instances. -/
theorem sparseCoreBundleRestartToolMachWith_isSpecOrdRestartOn (E : SparseCoreEnv)
    (lsfInit : LSFInit)
    (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ) (hConst : 1 ≤ spanConst)
    (Pred : ℕ → ℕ → ℕ → ℕ → DynamicInstance → Prop)
    (hParams : ∀ (k τ M N : ℕ) (D : DynamicInstance),
      Pred k τ M N D → SparsifyParamsLe (params M) (E.P_fn M))
    (hHyps : ∀ (k τ M N : ℕ) (D : DynamicInstance) (ord : ℕ → ℕ → List End),
      0 < k → (D.G 0).IsValid → D.IsValid τ → LengthsStable D τ →
      (∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e) → OrderedUpTo D τ 2 ord →
      (D.G 0).m ≤ M → (D.G 0).n ≤ N →
      (((Finset.Icc 1 τ).sum fun s => (D.U s).length : ℕ) : ℝ) ≤
        SparseCoreTool.updateThreshold k M N →
      Pred k τ M N D → BundleCoreHypsAtWith E lsfInit sparsify k M D) :
    (sparseCoreBundleRestartToolMachWith lsfInit E.C_lsst E.L sparsify params
        spanConst).IsSpecOrdRestartOn (bundleCoreParamsMachWith E spanConst) Pred := by
  intro k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hPred
  have hℓ : ∀ t ≤ τ, ∀ e ∈ (D.G t).E, 0 < D.ℓ t e := fun t ht e he =>
    ((hWeak t ht).2.2.2 e he).2.2.1
  have hH := hHyps k τ M N D ord hk hG₀ hD hLen hℓ hOrd hM hN hThresh hPred
  have hP := hParams k τ M N D hPred
  have h := bundleRestartWith_spec E lsfInit sparsify k τ M N D ord restarts Ψ c w
    hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hH
  have hNC := bundleRestartMachWith_nonCost_of_base lsfInit E.C_lsst E.L sparsify params spanConst
    k τ M N D ord restarts c w (bundleCoreParamsMachWith E spanConst)
    ⟨h.1, h.2.1, fun r hr p j' hpref => ⟨(h.2.2.1 r hr p j' hpref).1, (h.2.2.1 r hr p j' hpref).2.1⟩,
      h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
  have hR := bundleRestartMachWith_restartCost E lsfInit sparsify params spanConst hConst
    k τ M N D ord restarts Ψ c w hk hG₀ hD hWeak hOrd hM hN hrest hThresh hH hP
  have hT := bundleRestartMachWith_totalCost_le E lsfInit sparsify params spanConst hConst
    k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh hH hP
  exact ⟨hNC.1, hNC.2.1,
    fun r hr p j' hpref => ⟨(hNC.2.2.1 r hr p j' hpref).1, (hNC.2.2.1 r hr p j' hpref).2,
      (hR r hr p j' hpref).1, (hR r hr p j' hpref).2⟩,
    hNC.2.2.2.1, hNC.2.2.2.2.1, hNC.2.2.2.2.2, hT⟩

/-- `ToolNoReinsertOrdRestart` for the machine-cost tool. The property is about non-cost outputs
only, which agree with `sparseCoreBundleRestartToolWith` by `SparseCoreBundleNonMachEq`. -/
theorem sparseCoreBundleRestartToolMachWith_toolNoReinsertOrdRestart
    (lsfInit : LSFInit) (C_lsst : ℝ) (L : ℕ) (hL : 1 ≤ L)
    (P_fn : ℕ → SparsifyParams) (sparsify : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    (params : ℕ → SparsifyParams) (spanConst : ℕ)
    (hInit : ∀ k, 0 < k → ∀ j < k, IsValidLSFInitFor lsfInit C_lsst k j)
    (hSp : ∀ m, SparsifySpec m (P_fn m) (sparsify m)) :
    (sparseCoreBundleRestartToolMachWith lsfInit C_lsst L sparsify params
        spanConst).ToolNoReinsertOrdRestart := by
  intro k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh t ht1 htτ j hj
    e hePrev heCur hNoIns
  have hNM_prev := sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify
    params spanConst k M N D ord restarts (t - 1)
  have hNM_cur := sparseCoreBundleRestartToolMachWith_runOrd_nonMachEq lsfInit C_lsst L sparsify
    params spanConst k M N D ord restarts t
  rw [SparseCoreBundleNonMachEq.S_eq lsfInit C_lsst L sparsify params spanConst hNM_prev.2.2 j] at hePrev
  rw [SparseCoreBundleNonMachEq.S_eq lsfInit C_lsst L sparsify params spanConst hNM_cur.2.2 j] at heCur
  rw [congrFun hNM_cur.2.1 j] at hNoIns
  exact sparseCoreBundleRestartToolWith_toolNoReinsertOrdRestart lsfInit C_lsst L hL P_fn sparsify
    hInit hSp k τ M N D ord restarts Ψ c w hk hG₀ hD hLen hWeak hOrd hM hN hrest hThresh t ht1 htτ
    j hj e hePrev heCur hNoIns

end MinCostFlow.Chain.Ordered

end
