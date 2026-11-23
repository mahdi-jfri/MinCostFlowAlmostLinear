module

public import MinCostFlow.SparseCore.Program.AssemblyBranchFacts
public import MinCostFlow.SparseCore.Program.ReadBridge
public import MinCostFlow.SparseCore.Program.OutEditsModel
import MinCostFlow.SparseCore.BundleOutBatchSpec
import MinCostFlow.SparseCore.Program.OutEditsValid
import MinCostFlow.SparseCore.CompLSFBridge
import MinCostFlow.SparseCore.LSFInsertNonTree

/-!
# The model side of P10's update in the step of a branch (`AssemblyBranchStepReadModel`)

The step of a branch calls the update of the readout data (piece P10, `ReadBranchAt.step`) third,
after the first phase and P7's output step. The update asks model facts about the output batch
`U_S` of the step and about the data it leaves:
* `U_S` is a valid batch on the old output graph (`stepBundleTree_U_S_valid`, from `buildUSOrd_spec`
  as in `OutEditsModel.lean`);
* `U_S` fits the caps (`stepBundleTree_U_S_withinCaps`): its insertions are edges of the new output
  graph, and the new vertex of each of its splits is a vertex of the new output graph;
* the data after the update meet `ReadView.Inv` (`readView_step_inv`).

For the last one, the view after the update is `v.step U c U_S`. Its LSF `lsfViewStep v.lsf U c`
is the LSF of the model after the batch only up to `SameLSF` (`lsfViewStep_sameLSF`). So we prove
`ReadView.Inv` for the view of the model (`readView_inv_of_compLSF`) and carry it over along
`SameLSF` (`ReadView.Inv.of_sameLSF`). The stretch pairs of the view are kept by the update: an
inserted edge gets the pair `(1, 1)` and the stretch `1`, and the other edges keep both
(`pairs_applyBatch`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Read

/-! ## The output batch -/

section OutBatch

variable {depth : ℕ} (sparsify : ℕ → MGraph → MGraph → Embedding → DynSpanner.SparsifyOut)

/-- **The output batch is valid on the old output graph** (`buildUSOrd_spec`). -/
theorem stepBundleTree_U_S_valid {tr : BundleTreeState depth} {U : List Update}
    {ord ord' : ℕ → List End} (hready : OutStepReady sparsify tr U ord ord') :
    tr.S_cur.BatchIsValid (stepBundleTree sparsify tr U ord ord').U_S := by
  obtain ⟨C_lsst, ℓ₀, hI, hBU, ⟨ρ, σ, hρ, hσ, hrot⟩, hS_val, hS_V, hS_sub, hS_sub'⟩ := hready
  have hspec := buildUSOrd_spec hI hBU ρ σ hρ hσ hrot hS_val hS_V hS_sub hS_sub'.2.1
    (stepBundleTree sparsify tr U ord ord').D_total
  rw [stepBundleTree_U_S_eq]
  exact hspec.1

/-- The splits restricted to a set of kept edges contain no insertion. -/
private theorem restrictSplits_not_insert (keep : Finset ℕ) :
    ∀ (UC : List Update) {e a b : ℕ}, Update.insert e a b ∉ restrictSplits keep UC
  | [] => by simp [restrictSplits]
  | .split v v' St Sh :: UC => fun hu => by
    simp only [restrictSplits, List.mem_cons] at hu
    rcases hu with h | hu
    · exact Update.noConfusion h
    · exact restrictSplits_not_insert keep UC hu
  | .insert .. :: UC => restrictSplits_not_insert keep UC
  | .delete _ :: UC => restrictSplits_not_insert keep UC

/-- The new vertex of a split of a batch is a vertex of the graph after the batch, since the
split adds it and no update removes a vertex. -/
theorem split_new_mem_applyBatch : ∀ (G : MGraph) (W : List Update) {v v' : ℕ}
    {St Sh : Finset ℕ}, Update.split v v' St Sh ∈ W → v' ∈ (G.applyBatch W).V
  | _, [], _, _, _, _, h => absurd h List.not_mem_nil
  | G, u :: W, v, v', St, Sh, h => by
    rcases List.mem_cons.mp h with rfl | h
    · exact V_subset_applyBatch _ W (by simp [MGraph.applyUpdate])
    · exact split_new_mem_applyBatch (G.applyUpdate u) W h

/-- **The output batch fits the caps** when the new output graph does: its insertions are edges
of the new output graph (`outInsList`), its deletions need nothing, and the new vertex of each of
its splits is a vertex of the new output graph (`split_new_mem_applyBatch`). -/
theorem stepBundleTree_U_S_withinCaps {tr : BundleTreeState depth} {U : List Update}
    {ord ord' : ℕ → List End} {vCap eCap : ℕ}
    (hV : ∀ x ∈ (stepBundleTree sparsify tr U ord ord').state.S_cur.V, x < vCap)
    (hE : ∀ e ∈ (stepBundleTree sparsify tr U ord ord').state.S_cur.E, e < eCap) :
    BatchWithinCaps vCap eCap (stepBundleTree sparsify tr U ord ord').U_S := by
  intro u hu
  have hsplit : ∀ {v v' : ℕ} {St Sh : Finset ℕ},
      Update.split v v' St Sh ∈ (stepBundleTree sparsify tr U ord ord').U_S → v' < vCap :=
    fun h => hV _ (split_new_mem_applyBatch tr.S_cur _ h)
  have hu' := hu
  rw [stepBundleTree_U_S_split] at hu'
  rcases List.mem_append.mp hu' with hu' | hu'
  · cases u with
    | delete e => trivial
    | split v v' St Sh => exact hsplit hu
    | insert e a b =>
      exfalso
      rcases List.mem_append.mp hu' with h | h
      · obtain ⟨_, -, h⟩ := List.mem_map.mp h
        exact Update.noConfusion h
      · exact restrictSplits_not_insert _ _ h
  · obtain ⟨e, he, rfl⟩ := List.mem_map.mp hu'
    simp only [outInsList, Finset.mem_sort, Finset.mem_sdiff] at he
    exact hE e he.1

end OutBatch

/-! ## The stretch pairs -/

/-- **The update keeps the stretch pairs.** If every edge of `G` has a positive denominator and
its pair gives its stretch, the same holds after the batch `U` for the pairs and the stretches of
the update (`pairViewUpdate`, `wstrViewUpdate`): an inserted edge gets the pair `(1, 1)` and the
stretch `1`, and every other edge of the new graph was an edge of the old graph with the same
pair and stretch. -/
theorem pairs_applyBatch : ∀ (U : List Update) (G : MGraph) (num den : ℕ → ℤ) (wstr : ℕ → ℝ),
    (∀ e ∈ G.E, 0 < den e ∧ (num e : ℝ) / den e = wstr e) →
    ∀ e ∈ (G.applyBatch U).E, 0 < U.foldl pairViewUpdate den e ∧
      ((U.foldl pairViewUpdate num e : ℤ) : ℝ) / (U.foldl pairViewUpdate den e : ℤ) =
        U.foldl wstrViewUpdate wstr e
  | [], _, _, _, _, h => h
  | u :: U, G, num, den, wstr, h => by
    refine pairs_applyBatch U (G.applyUpdate u) (pairViewUpdate num u) (pairViewUpdate den u)
      (wstrViewUpdate wstr u) ?_
    intro e he
    cases u with
    | insert e₀ a b =>
      by_cases hee : e = e₀
      · subst hee
        simp [pairViewUpdate, wstrViewUpdate]
      · have he' : e ∈ G.E := by
          simpa [MGraph.applyUpdate, hee] using he
        simpa [pairViewUpdate, wstrViewUpdate, Function.update_of_ne hee] using h e he'
    | delete e₀ =>
      have he' : e ∈ G.E := (Finset.mem_erase.mp he).2
      simpa [pairViewUpdate, wstrViewUpdate] using h e he'
    | split v v' St Sh =>
      simpa [pairViewUpdate, wstrViewUpdate] using h e he

/-! ## `ReadView.Inv` -/

/-- **`ReadView.Inv` depends on the LSF only up to `SameLSF`**: the tree and the forest are the
same graphs up to `SameGraph`, so their vertices, edges, ends on their edges and connectivity
agree, and the roots and the stretches are equal. -/
theorem ReadView.Inv.of_sameLSF {vCap eCap tCap : ℕ} {v : ReadView} {lsf' : LSF}
    (h : v.Inv vCap eCap tCap) (hs : SameLSF v.lsf lsf') :
    ({ v with lsf := lsf' } : ReadView).Inv vCap eCap tCap := by
  obtain ⟨hG, hGV, hGE, het, hTv, hTV, hTE, hTends, hFV, hFsub, hRV, hroot, hS, hSV, hSE,
    hpairs⟩ := h
  obtain ⟨hT, hF, hR, hw⟩ := hs
  refine ⟨hG, hGV, hGE, het, ?_, hT.1 ▸ hTV, ?_, ?_, hF.1 ▸ hFV, ?_, hR ▸ hRV, ?_, hS, hSV, hSE,
    hw ▸ hpairs⟩
  · intro e he
    have he' : e ∈ v.lsf.T.E := hT.2.1 ▸ he
    obtain ⟨h1, h2⟩ := hT.2.2 e he'
    rw [← h1, ← h2, ← hT.1]
    exact hTv e he'
  · intro e he
    exact hTE e (hT.2.1 ▸ he)
  · intro e he heG
    have he' : e ∈ v.lsf.T.E := hT.2.1 ▸ he
    obtain ⟨h1, h2⟩ := hT.2.2 e he'
    rw [← h1, ← h2]
    exact hTends e he' heG
  · obtain ⟨hsV, hsE, hsends⟩ := hFsub
    refine ⟨hF.1 ▸ hsV, hF.2.1 ▸ hsE, fun e he => ?_⟩
    have he' : e ∈ v.lsf.F.F.E := hF.2.1 ▸ he
    obtain ⟨h1, h2⟩ := hF.2.2 e he'
    obtain ⟨h3, h4⟩ := hsends e he'
    exact ⟨h1 ▸ h3, h2 ▸ h4⟩
  · intro x hx
    obtain ⟨r, ⟨hrR, hrc⟩, huniq⟩ := hroot x hx
    refine ⟨r, ⟨hR ▸ hrR, (hF.connected_iff x r).mp hrc⟩, fun r' hr' => ?_⟩
    exact huniq r' ⟨hR ▸ hr'.1, (hF.connected_iff x r').mpr hr'.2⟩

/-- **The data after P10's update meet `ReadView.Inv`.** Let `v` be the view of the branch before
the step: the graph `cs.G`, the LSF `cs.lsf`, the output graph `S`, and pairs that give the
stretches of `cs`. After the batch `U`, the change record `c` of the LSF and the output batch
`U_S`, the view `v.step U c U_S` meets `ReadView.Inv` when the LSF state after the batch meets
`CompLSFInv`, its names fit the caps, the new output graph `S.applyBatch U_S` is valid with names in
the caps, and `eCap ≤ tCap`. The proof builds `ReadView.Inv` for the view of the model after the
batch (`readView_inv_of_compLSF`, with the pairs from `pairs_applyBatch`) and carries it over along
`SameLSF` (`lsfViewStep_sameLSF`). -/
theorem readView_step_inv {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {vCap eCap tCap : ℕ} {cs : CompLSFState}
    {S : MGraph} {num den : ℕ → ℤ} {U U_S : List Update} {c : LSFChange}
    (hI : CompLSFInv C_lsst ℓ₀ cs) (hU : cs.G.BatchIsValid U)
    (hc : c.Exact cs.lsf (compLSFBatch cs U).lsf)
    (hpairs : ∀ e ∈ cs.G.E, 0 < den e ∧ (num e : ℝ) / den e = cs.lsf.wstr e)
    (hGV : ∀ x ∈ (compLSFBatch cs U).G.V, x < vCap) (hGE : ∀ e ∈ (compLSFBatch cs U).G.E, e < eCap)
    (het : eCap ≤ tCap) (hSval : (S.applyBatch U_S).IsValid)
    (hSV : ∀ x ∈ (S.applyBatch U_S).V, x < vCap) (hSE : ∀ e ∈ (S.applyBatch U_S).E, e < eCap) :
    (ReadView.step ⟨cs.G, cs.lsf, S, num, den⟩ U c U_S).Inv vCap eCap tCap := by
  have hI' := compLSFBatch_inv hI hU
  have hG' := compLSFBatch_G cs U
  have hTE : ∀ e ∈ (compLSFBatch cs U).T.E, e < tCap := fun e he =>
    lt_of_lt_of_le (hGE e (compLSF_T_E_subset_G _ he)) het
  have hp' : ∀ e ∈ (compLSFBatch cs U).G.E, 0 < U.foldl pairViewUpdate den e ∧
      ((U.foldl pairViewUpdate num e : ℤ) : ℝ) / (U.foldl pairViewUpdate den e : ℤ) =
        (compLSFBatch cs U).wstrGlobal e := by
    intro e he
    have h := pairs_applyBatch U cs.G num den cs.lsf.wstr hpairs e (hG' ▸ he)
    have hw : (compLSFBatch cs U).wstrGlobal = U.foldl wstrViewUpdate cs.lsf.wstr :=
      compLSFBatch_wstr_eq cs U
    rw [hw]
    exact h
  have hinv := readView_inv_of_compLSF (num := U.foldl pairViewUpdate num)
    (den := U.foldl pairViewUpdate den) hI' hGV hGE het hTE hSval hSV hSE hp'
  have hs : SameLSF (compLSFBatch cs U).lsf (lsfViewStep cs.lsf U c) :=
    (lsfViewStep_sameLSF hI hU hc).symm
  have h2 := ReadView.Inv.of_sameLSF hinv hs
  simp only [ReadView.step]
  rw [← hG']
  exact h2

/-! ## The size of the change record -/

/-- The number of entries of the change record of an LSF view from `lsf` to `lsf'`: the new
roots and the forest edges that leave the forest (`LSFChange.Exact`). -/
def lsfChangeSize (lsf lsf' : LSF) : ℕ :=
  (lsf'.F.R \ lsf.F.R).card + (lsf.F.F.E \ lsf'.F.F.E).card

/-- An exact change record has `lsfChangeSize` entries: it lists each new root and each leaving
forest edge once. -/
theorem lsfChange_size_eq {c : LSFChange} {lsf lsf' : LSF} (hc : c.Exact lsf lsf') :
    c.size = lsfChangeSize lsf lsf' := by
  obtain ⟨hn1, he1, hn2, he2⟩ := hc
  rw [LSFChange.size, lsfChangeSize, ← he1, ← he2, List.toFinset_card_of_nodup hn1,
    List.toFinset_card_of_nodup hn2]

/-- The change record has at most `vCap + eCap` entries when the new roots are below `vCap` and
the old forest edges are below `eCap`. -/
theorem lsfChangeSize_le {lsf lsf' : LSF} {vCap eCap : ℕ} (hR : ∀ x ∈ lsf'.F.R, x < vCap)
    (hF : ∀ e ∈ lsf.F.F.E, e < eCap) : lsfChangeSize lsf lsf' ≤ vCap + eCap := by
  have h1 : (lsf'.F.R \ lsf.F.R).card ≤ vCap := by
    calc (lsf'.F.R \ lsf.F.R).card ≤ (Finset.range vCap).card :=
          Finset.card_le_card fun x hx =>
            Finset.mem_range.mpr (hR x (Finset.mem_sdiff.mp hx).1)
      _ = vCap := Finset.card_range vCap
  have h2 : (lsf.F.F.E \ lsf'.F.F.E).card ≤ eCap := by
    calc (lsf.F.F.E \ lsf'.F.F.E).card ≤ (Finset.range eCap).card :=
          Finset.card_le_card fun e he =>
            Finset.mem_range.mpr (hF e (Finset.mem_sdiff.mp he).1)
      _ = eCap := Finset.card_range eCap
  unfold lsfChangeSize
  omega

end MinCostFlow.SparseCore.Program
