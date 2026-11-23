module

public import MinCostFlow.HierPaths.InitCounters
public import MinCostFlow.HierPaths.InitProgBoundWords

/-!
# The 24 writers of the block

`initWriters VC VX VL Wm` lists the 24 writers: the header from the word procedures `VC`,
`VX`, `VL` for `numConn`, `ξ`, `λ`; the owners; the 11 writers `Wm` of sections 2–12; and the
11 finished writers of sections 13–23. `initWriters_secs` proves the section hypothesis of
`buildProc_spec` from what `VC`, `VX`, `VL` and `Wm` must give.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The 24 writers of the block. -/
def initWriters {a : ℕ} (VC VX VL : ValW a) (Wm : List (SecW a)) : List (SecW a) :=
  [headerW VC VX VL, ownerW a] ++ Wm ++
    [zeroPowW a, zeroPowW a, zeroValW VC, zeroGraphW a 1 (by norm_num),
      zeroGraphW a 0 (by norm_num), countersW a, countersW a, zeroGraphW a 0 (by norm_num),
      pairCurW a, zeroGraphW a 0 (by norm_num), stackW a]

theorem length_initWriters {a : ℕ} (VC VX VL : ValW a) {Wm : List (SecW a)}
    (hm : Wm.length = 11) : (initWriters VC VX VL Wm).length = 24 := by
  simp [initWriters, hm]

/-- **The sections of the 24 writers.** -/
theorem initWriters_secs {a : ℕ} {VC VX VL : ValW a} {Wm : List (SecW a)} {S : StaticData}
    {G : Graph} {gAddr phiNum phiDen M h h₁ : ℕ}
    (hC : VC.val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.A.C.numConn)
    (hX : VX.val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.ξ)
    (hL : VL.val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.lam)
    (hm : Wm.map (fun W => W.l S G [gAddr, phiNum, phiDen, M, h, h₁]) =
      ((initConcrete S a (initAbs phiNum phiDen M G)).sections.drop 2).take 11) :
    (initWriters VC VX VL Wm).map (fun W => W.l S G [gAddr, phiNum, phiDen, M, h, h₁]) =
      (initConcrete S a (initAbs phiNum phiDen M G)).sections := by
  have hs := (List.take_append_drop 13 (initConcrete S a (initAbs phiNum phiDen M G)).sections)
  have hs2 := (List.take_append_drop 2
    ((initConcrete S a (initAbs phiNum phiDen M G)).sections.take 13))
  rw [← hs, ← hs2, List.take_take, List.drop_take]
  simp only [initWriters, List.map_append]
  simp only [show min 2 13 = 2 from rfl, show 13 - 2 = 11 from rfl] 
  rw [← hm]
  congr 1
  · congr 1
    have h0 := headerW_l (VC := VC) (VX := VX) (VL := VL) hC hX hL
    have h1 := initConcrete_section_owner S a (initAbs phiNum phiDen M G)
    simp only [List.map_cons, List.map_nil]
    rw [h0]
    simp only [ownerW]
    rw [← h1]
    simp [HierConcrete.sections]
  · simp [HierConcrete.sections, zeroValW, zeroPowW, zeroGraphW, countersW, pairCurW, stackW,
      hC, initConcrete, initAbs, DelState.init, LossState.init, bitsList, tabList,
      List.map_const', HierConcrete.n, HierConcrete.m, HierConcrete.depth, stackWords,
      StaticData.model, staticArrays, connSystem, Graph.encode, countersList]

/-- **The builder from its pieces.** `BuildProcSpec` holds for `buildProc` of the 24
writers once `VC`, `VX`, `VL` give `numConn`, `ξ`, `λ`, the writers `Wm` write sections 2–12,
and the cost and space bounds hold. -/
theorem initBuildProc_spec {a K : ℕ} {sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ} {C c : ℕ}
    (VC VX VL : ValW a) (Wm : List (SecW a)) (hlen : Wm.length = 11)
    (hC : ∀ S G gAddr phiNum phiDen M h h₁, VC.val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.A.C.numConn)
    (hX : ∀ S G gAddr phiNum phiDen M h h₁, VX.val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.ξ)
    (hL : ∀ S G gAddr phiNum phiDen M h h₁, VL.val S G [gAddr, phiNum, phiDen, M, h, h₁] =
      (initConcrete S a (initAbs phiNum phiDen M G)).H.lam)
    (hm : ∀ S G gAddr phiNum phiDen M h h₁,
      S.Good a (dOf phiNum phiDen) M G →
      Wm.map (fun W => W.l S G [gAddr, phiNum, phiDen, M, h, h₁]) =
        ((initConcrete S a (initAbs phiNum phiDen M G)).sections.drop 2).take 11)
    (hsp : ∀ S G gAddr phiNum phiDen M h h₁, 1 ≤ phiNum → phiNum ≤ phiDen →
      S.Good a (dOf phiNum phiDen) M G →
      (initBlock S a G phiNum phiDen M).length +
        ((initWriters VC VX VL Wm).map fun W =>
          W.scratch S G [gAddr, phiNum, phiDen, M, h, h₁]).sum ≤ sR phiNum phiDen G.n G.m M)
    (hcost : ∀ S G gAddr phiNum phiDen M h h₁,
      S.Good a (dOf phiNum phiDen) M G →
      ((initWriters VC VX VL Wm).map fun W =>
          W.cost S G [gAddr, phiNum, phiDen, M, h, h₁] + 40).sum + 30 ≤
        K * (initRestSteps S.H S.x S.b S.owner S.label G.n G.m +
          (initBlock S a G phiNum phiDen M).length))
    (hform : SpaceForm a sR C c) :
    BuildProcSpec a (buildProc (initWriters VC VX VL Wm)) K sR C c :=
  buildProc_spec _ (length_initWriters VC VX VL hlen)
    (fun S G gAddr phiNum phiDen M h h₁ hgood => initWriters_secs (hC S G gAddr phiNum phiDen M h h₁)
      (hX S G gAddr phiNum phiDen M h h₁) (hL S G gAddr phiNum phiDen M h h₁)
      (hm S G gAddr phiNum phiDen M h h₁ hgood))
    hsp hcost hform

/-- The block builder with the three header procedures fixed. -/
def hierInitBuilder (a : ℕ) (ha : 1 ≤ a) (Wm : List (SecW a)) : HierProc :=
  buildProc (initWriters (numConnW a) (initBoundW a ha true) (initBoundW a ha false) Wm)

/-- The verified header procedures supply the header and the number of initial eligibility bits.
The remaining writers supply sections 2 through 12. -/
theorem hierInitBuilder_spec {a K C c : ℕ} {sR : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ}
    (ha : 1 ≤ a) (Wm : List (SecW a)) (hlen : Wm.length = 11)
    (hm : ∀ S G gAddr phiNum phiDen M h h₁,
      S.Good a (dOf phiNum phiDen) M G →
      Wm.map (fun W => W.l S G [gAddr, phiNum, phiDen, M, h, h₁]) =
        ((initConcrete S a (initAbs phiNum phiDen M G)).sections.drop 2).take 11)
    (hsp : ∀ S G gAddr phiNum phiDen M h h₁, 1 ≤ phiNum → phiNum ≤ phiDen →
      S.Good a (dOf phiNum phiDen) M G →
      (initBlock S a G phiNum phiDen M).length +
        ((initWriters (numConnW a) (initBoundW a ha true) (initBoundW a ha false) Wm).map fun W =>
          W.scratch S G [gAddr, phiNum, phiDen, M, h, h₁]).sum ≤ sR phiNum phiDen G.n G.m M)
    (hcost : ∀ S G gAddr phiNum phiDen M h h₁,
      S.Good a (dOf phiNum phiDen) M G →
      ((initWriters (numConnW a) (initBoundW a ha true) (initBoundW a ha false) Wm).map fun W =>
          W.cost S G [gAddr, phiNum, phiDen, M, h, h₁] + 40).sum + 30 ≤
        K * (initRestSteps S.H S.x S.b S.owner S.label G.n G.m +
          (initBlock S a G phiNum phiDen M).length))
    (hform : SpaceForm a sR C c) :
    BuildProcSpec a (hierInitBuilder a ha Wm) K sR C c :=
  initBuildProc_spec _ _ _ Wm hlen
    (fun S G gAddr phiNum phiDen M h h₁ => numConnW_init S a (initAbs phiNum phiDen M G)
      [gAddr, phiNum, phiDen, M, h, h₁])
    (fun S G => initBoundW_xi S a ha G) (fun S G => initBoundW_lam S a ha G)
    hm hsp hcost hform

end MinCostFlow.HierPaths

end
