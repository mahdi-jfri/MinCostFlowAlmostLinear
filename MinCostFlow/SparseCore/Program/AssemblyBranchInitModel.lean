module

public import MinCostFlow.SparseCore.Program.AssemblyBranchInitIface
import MinCostFlow.SparseCore.Program.ReadBridge
import MinCostFlow.SparseCore.CompLSFBridge
import MinCostFlow.SparseCore.Program.AssemblyBranchRestartSpace

/-!
# The readout data at the init of a branch: the model side (`AssemblyBranchInitModel`)

The init of a branch calls P10's init (`ReadBranchAt.init`) on the view
`⟨G, lsf, S, num, den⟩` of the new branch state. P10's init asks that the view meets
`ReadView.Inv`, and its cost and space grow with the size `readInitSize` of the view. This file
proves both from the facts of the model (`AsmBrModelFacts`):
* `readInitSize_le_facts`: the size is at most `4 G.n + 4 G.m`. The tree `T` and the forest `F`
  have the vertices of `G` and edges among those of `G`, the roots are vertices of `G`, and `S`
  is a subgraph of the core graph, whose vertices are the roots and whose edges are edges of `G`.
  So `readInitSize_le_caps` bounds it by `4 vCap + 4 eCap`.
* `readView_inv_of_facts`: the view meets `ReadView.Inv` when the tree edges lie below `tCap`,
  `eCap ≤ tCap`, and the pairs `num`, `den` give the stretches. P4's export gives these three.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Read

/-- **The size of the view of a branch** is at most `4 G.n + 4 G.m` on the model. -/
theorem readInitSize_le_facts {depth : ℕ} {impl : SparsifyImpl} {vCap eCap : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} (hF : AsmBrModelFacts impl vCap eCap tr ord)
    (num den : ℕ → ℤ) :
    readInitSize ⟨tr.cs.G, tr.cs.lsf, tr.S_cur, num, den⟩ ≤ 4 * tr.cs.G.n + 4 * tr.cs.G.m := by
  obtain ⟨-, ⟨C_lsst, ℓ₀, hI, -⟩, hScur, -⟩ := hF
  have hRS := compLSF_RF_isRSF hI
  have hTn : tr.cs.T.n = tr.cs.G.n := rfl
  have hTm : tr.cs.T.m ≤ tr.cs.G.m := Finset.card_le_card fun e he =>
    (Finset.mem_sdiff.mp (Finset.mem_inter.mp he).2).1
  have hFm : tr.cs.RF.F.m ≤ tr.cs.G.m := Finset.card_le_card hRS.2.2.2.2.2.1
  have hR : tr.cs.RF.R.card ≤ tr.cs.G.n := Finset.card_le_card hRS.2.2.1
  have hSn : tr.S_cur.n ≤ tr.cs.G.n := by
    unfold MGraph.n; rw [hScur.2.1]; exact hR
  have hSm : tr.S_cur.m ≤ tr.cs.G.m := by
    refine Finset.card_le_card fun e he => ?_
    exact (Finset.mem_sdiff.mp (hScur.2.2.2.1.2.1 he)).1
  unfold readInitSize
  have e1 : tr.cs.lsf.T = tr.cs.T := rfl
  have e2 : tr.cs.lsf.F = tr.cs.RF := rfl
  simp only [e1, e2]
  omega

/-- **The size of the view of a branch in the caps**: at most `4 vCap + 4 eCap`, since the names
of the vertices of `G` lie below `vCap` and those of its edges below `eCap`. -/
theorem readInitSize_le_caps {depth : ℕ} {impl : SparsifyImpl} {vCap eCap : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} (hF : AsmBrModelFacts impl vCap eCap tr ord)
    (num den : ℕ → ℤ) :
    readInitSize ⟨tr.cs.G, tr.cs.lsf, tr.S_cur, num, den⟩ ≤ 4 * vCap + 4 * eCap := by
  have h := readInitSize_le_facts hF num den
  have hn : tr.cs.G.n ≤ vCap := card_le_of_forall_mem_lt hF.2.2.2.2.2.2.2.1
  have hm : tr.cs.G.m ≤ eCap := card_le_of_forall_mem_lt hF.2.2.2.2.2.2.2.2.1
  omega

/-- **The view of a branch meets `ReadView.Inv`** on the model, when `eCap ≤ tCap`, the tree edges
lie below `tCap` and the pairs `num`, `den` give the stretches of the edges of `G`. -/
theorem readView_inv_of_facts {depth : ℕ} {impl : SparsifyImpl} {vCap eCap tCap : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End} (hF : AsmBrModelFacts impl vCap eCap tr ord)
    {num den : ℕ → ℤ} (het : eCap ≤ tCap) (hTE : ∀ e ∈ tr.cs.lsf.T.E, e < tCap)
    (hpairs : ∀ e ∈ tr.cs.G.E, 0 < den e ∧ (num e : ℝ) / den e = tr.cs.lsf.wstr e) :
    ReadView.Inv vCap eCap tCap ⟨tr.cs.G, tr.cs.lsf, tr.S_cur, num, den⟩ := by
  obtain ⟨-, ⟨C_lsst, ℓ₀, hI, -⟩, hScur, -, hSval, -, -, hGV, hGE, hSE⟩ := hF
  have hRS := compLSF_RF_isRSF hI
  have hSV : ∀ x ∈ tr.S_cur.V, x < vCap := fun x hx => by
    rw [hScur.2.1] at hx
    exact hGV x (hRS.2.2.1 hx)
  exact readView_inv_of_compLSF hI hGV hGE het hTE hSval hSV hSE hpairs

end MinCostFlow.SparseCore.Program
