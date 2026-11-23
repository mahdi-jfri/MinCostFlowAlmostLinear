module

public import MinCostFlow.MinRatio.WireSelectEvalKeyProofs
public import MinCostFlow.MinRatio.WireSelectUpdateEdge

/-!
# The key evaluator inside the select procedures (`WireSelectEvalKeyBridge`)

`selectProcessEdge_meetsContract` (`WireSelectUpdateEdge.lean`) takes the key evaluator as a
hypothesis `heval`: some procedure meets `evalCandKeyContract`. The procedure
`evalKeyModule b h` meets `evalCandKeyContractRepaired`. The two contracts agree:
* `SelectCoreLenInv` stores `C.chainLen ℓ (j + 1)` on `(C.G j).E`;
* `evalCandKeyContract.pre` asks `SelectLevelMetaBounded mem mloc C scratch`, and
  `selectProcessEdge_meetsContract` gets it from `SelectMetaDisjoint` and its frame hypothesis
  (`selectLevelMetaBounded_of_frame`).

So the two contracts are the same, and `evalKeyModule b h` discharges the hypothesis `heval`.

* `evalCandKeyContract_eq_repaired`: the two contracts are equal by definition.
* `evalKeyModule_meetsContract`: `evalKeyModule b h` meets `evalCandKeyContract`.
* `selectProcessEdge_meetsContract_evalKey`: `selectProcessEdgeBody b upsert delIf` meets
  `selectProcessEdgeContract`, with `evalKeyModule b h` placed at `b` in the program instead of
  the hypothesis `heval`.
-/

public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-- `evalCandKeyContract` is `evalCandKeyContractRepaired`: the two core-length
invariants are the same, and both preconditions ask `SelectLevelMetaBounded`. -/
theorem evalCandKeyContract_eq_repaired (w h P : ℕ) (mloc : SelectLevelMetaLoc)
    (C : TreeChain) (g ℓ : ℕ → ℝ) (φ coreLen : ℕ → ℕ → ℝ) (evalSpace evalCost : ℕ) :
    evalCandKeyContract w h P mloc C g ℓ φ coreLen evalSpace evalCost =
      evalCandKeyContractRepaired w h P mloc C g ℓ φ coreLen evalSpace evalCost := rfl

/-- **The key evaluator meets `evalCandKeyContract`.** This is
`evalKeyModule_meetsContract_repaired` through
`evalCandKeyContract_eq_repaired`. The hypotheses are those of the chain and of the fit of the
keys in `Lk` limbs. -/
theorem evalKeyModule_meetsContract
    {w h P b maxEmbLen : ℕ} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ} {p : Program}
    (hh0 : 0 < h) (hw2h : 2 * h + 2 ≤ w)
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hSpan : C.LastLevelSpans)
    (hℓPos : ∀ f ∈ (C.G 0).E, 0 < ℓ f)
    (hEmbBd : ∀ lvl < C.d, ∀ e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E,
      (C.activeEmb lvl e).length ≤ maxEmbLen)
    (hFit : CandidateKeysFit h P mloc.pLast mloc.Lk C g ℓ)
    (hAt : p.HasAt b (evalKeyModule b h)) :
    MeetsContract w p b
      (evalCandKeyContract w h P mloc C g ℓ φ coreLen
        (evalKeySpace C.d maxEmbLen mloc.Lk) (evalKeyCost C.d maxEmbLen mloc.Lk)) := by
  rw [evalCandKeyContract_eq_repaired]
  exact evalKeyModule_meetsContract_repaired hh0 hw2h hH hSpan hℓPos hEmbBd hFit hAt

/-- **One select edge, with the key evaluator in the program.** `selectProcessEdgeBody b upsert
delIf` meets `selectProcessEdgeContract` with the space and the cost of `evalKeyModule`, when
`evalKeyModule b h` lies at `b` in the program. `evalKeyModule_meetsContract`
discharges the hypothesis `heval` of `selectProcessEdge_meetsContract`. -/
theorem selectProcessEdge_meetsContract_evalKey {w h P proc b upsert delIf maxEmbLen : ℕ}
    {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C : TreeChain} {G : MGraph} {g ℓ : ℕ → ℝ} {σ σ_mwu γ_ℓ γ_c : ℝ}
    {φ coreLen : ℕ → ℕ → ℝ} {p : Program}
    (hp : p.procs[proc]? = some (selectProcessEdgeBody b upsert delIf))
    (hAt : p.HasAt b (evalKeyModule b h))
    (hh0 : 0 < h) (hw2h : 2 * h + 2 ≤ w)
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c)
    (hSpan : C.LastLevelSpans)
    (hℓPos : ∀ f ∈ (C.G 0).E, 0 < ℓ f)
    (hEmbBd : ∀ lvl < C.d, ∀ e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E,
      (C.activeEmb lvl e).length ≤ maxEmbLen)
    (hFit : CandidateKeysFit h P mloc.pLast mloc.Lk C g ℓ)
    (hups : ∀ size, MeetsContract w p upsert (heapUpsertContract w h loc size))
    (hdelIf : ∀ size, MeetsContract w p delIf (heapDeleteIfLevelContract w h loc size)) :
    MeetsContract w p proc
      (selectProcessEdgeContract w h P loc mloc C g ℓ φ coreLen
        (evalKeySpace C.d maxEmbLen mloc.Lk) (evalKeyCost C.d maxEmbLen mloc.Lk)) :=
  selectProcessEdge_meetsContract hp
    (evalKeyModule_meetsContract hh0 hw2h hH hSpan hℓPos hEmbBd hFit hAt) hups hdelIf

end MinCostFlow.MinRatio
