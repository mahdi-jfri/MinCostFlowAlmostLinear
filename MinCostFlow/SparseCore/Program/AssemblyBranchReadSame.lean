module

public import MinCostFlow.SparseCore.Program.ReadBridge
public import MinCostFlow.SparseCore.Program.ReadRep

/-!
# The readout data under a change of the LSF up to `SameLSF` (`AssemblyBranchReadSame`)

After a step, the update of P10 (`ReadBranchAt.step`) leaves the readout data holding the view
`lsfViewStep v.lsf U c`. This LSF is not equal to the LSF of the model after the batch, but it has
`SameLSF` with it (`lsfViewStep_sameLSF`, `ReadBridge.lean`): the two agree on the tree and the
forest up to `SameGraph`, and on the roots and the stretch table.

The representation of a branch keeps the LSF of the model itself in the view of the readout data.
This file shows that the data of P10 (`readRep`) hold any view whose LSF has `SameLSF` with the
stored one, with the same cells and the same potential (`readRep_of_sameLSF`). So the branch can
replace the LSF of P10's view by the LSF of the model after each step.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program.Read

open MinCostFlow MinCostFlow.LSF MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program

/-- The live part of the tree depends only on the edges of the tree. -/
theorem liveT_of_sameGraph {G T T' : MGraph} (hs : SameGraph T T') : liveT G T = liveT G T' := by
  simp only [liveT, hs.2.1]

/-- The frozen part of the tree changes only up to `SameGraph` with the tree. -/
theorem frozenT_of_sameGraph {G T T' : MGraph} (hs : SameGraph T T') :
    SameGraph (frozenT G T) (frozenT G T') := by
  refine ⟨rfl, by simp only [frozenT, hs.2.1], fun e he => ?_⟩
  have heT : e ∈ T.E := (Finset.mem_sdiff.mp he).1
  exact hs.2.2 e heT

/-- `ReadKeep` depends on the LSF only up to `SameLSF`. -/
theorem ReadKeep.of_sameLSF {v : ReadView} {lsf' : LSF} (hk : ReadKeep v)
    (hs : SameLSF v.lsf lsf') : ReadKeep { v with lsf := lsf' } := by
  obtain ⟨hTV, hTE, hFV, hFsub⟩ := hk
  obtain ⟨hT, hF, -, -⟩ := hs
  refine ⟨hT.1 ▸ hTV, fun e he heG => ?_, hF.1 ▸ hFV, ?_⟩
  · have he' : e ∈ v.lsf.T.E := hT.2.1 ▸ he
    obtain ⟨h1, h2⟩ := hT.2.2 e he'
    obtain ⟨h3, h4⟩ := hTE e he' heG
    exact ⟨h1 ▸ h3, h2 ▸ h4⟩
  · obtain ⟨hsV, hsE, hsends⟩ := hFsub
    refine ⟨hF.1 ▸ hsV, hF.2.1 ▸ hsE, fun e he => ?_⟩
    have he' : e ∈ v.lsf.F.F.E := hF.2.1 ▸ he
    obtain ⟨h1, h2⟩ := hF.2.2 e he'
    obtain ⟨h3, h4⟩ := hsends e he'
    exact ⟨h1 ▸ h3, h2 ▸ h4⟩

/-- `ReadRecAt` depends on the LSF only up to `SameLSF`. -/
theorem ReadRecAt.of_sameLSF {mem : ℕ → ℕ} {r vCap eCap tCap L_w P : ℕ} {v : ReadView}
    {q : ReadPtrs} {lsf' : LSF} (hrec : ReadRecAt mem r vCap eCap tCap L_w P v q)
    (hs : SameLSF v.lsf lsf') : ReadRecAt mem r vCap eCap tCap L_w P { v with lsf := lsf' } q := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, hT, hF, hR, hSv, hPr, hSc, hG⟩ := hrec
  exact ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, DynGraphAt.of_same hT hs.1, DynGraphAt.of_same hF hs.2.1,
    hs.2.2.1 ▸ hR, hs.2.2.2 ▸ hSv, hPr, hSc, hG⟩

/-- **The data of P10 hold a view whose LSF has `SameLSF` with the stored one**, with the same
pointers, so the same cells, and the same potential (`treePot_congr`). -/
theorem readRep_of_sameLSF {vCap eCap tCap L_w P r : ℕ} {v : ReadView} {y : ReadConc}
    {mem : ℕ → ℕ} {lsf' : LSF} (hrep : (readRep vCap eCap tCap L_w P).rep r v y mem)
    (hs : SameLSF v.lsf lsf') :
    (readRep vCap eCap tCap L_w P).rep r { v with lsf := lsf' }
        { y with view := { v with lsf := lsf' } } mem ∧
      (readRep vCap eCap tCap L_w P).phi r { y with view := { v with lsf := lsf' } } mem =
        (readRep vCap eCap tCap L_w P).phi r y mem ∧
      (∀ a, (readRep vCap eCap tCap L_w P).foot r { y with view := { v with lsf := lsf' } } a ↔
        (readRep vCap eCap tCap L_w P).foot r y a) := by
  obtain ⟨hv, hlay, hkeep, hrec, h9, h10, hlive, hfrz⟩ := hrep
  have hl : liveT v.G v.lsf.T = liveT v.G lsf'.T := liveT_of_sameGraph hs.1
  have hf : SameGraph (frozenT v.G v.lsf.T) (frozenT v.G lsf'.T) := frozenT_of_sameGraph hs.1
  refine ⟨⟨rfl, hlay, hkeep.of_sameLSF hs, hrec.of_sameLSF hs, h9, h10, ?_, DynGraphAt.of_same hfrz hf⟩,
    ?_, fun a => Iff.rfl⟩
  · simpa only [hl] using hlive
  · simp only [readRep_phi]
    rw [hv]
    exact congrArg (readPotMul * ·) (treePot_congr rfl (hl ▸ SameGraph.refl _) hf)

end MinCostFlow.SparseCore.Program.Read
