module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpaceTasks
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepSpacePre
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNCDefs

import MinCostFlow.SparseCore.Program.AssemblyFirstStepNCParts
import MinCostFlow.SparseCore.Program.AssemblyFirstTourStepModel
import MinCostFlow.SparseCore.Program.AssemblyBranchStepModel
import Mathlib.Tactic

/-!
# The room of Phase 4 and the bound of the last result (`AssemblyFirstStepSpaceP4`)

The pieces of the first step ask two space facts on Phase 4:
* `hSp4`: from the end `hEnd₃` of Phase 3, the cells that Phase 4 may use fit in a word
  (`AsmFsP4Room`);
* `hSpG`: the value that Phase 4 returns is at most `A.h + space X` (`AsmFsSpaceGoal`).

Both follow from one bound (`asmFirstStep_p4_end_le`): `hEnd₃` plus the cells of Phase 4 is at
most `A.h + space X`, where `space := asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp`. To get it,
we bound `hEnd₃` by the start plus the spaces of Phases 1 to 3 (`asmFirstStep_p4_spaceFacts`), and
then the sum of the spaces of all four phases by `space X` (`asmFirstStepSpace_le_poly_std`). The
second lemma is stated on the side record `x.xRest` before the step, and Phase 4 works on the side
record `y'` after Phase 2. They have the same caps (`asmFirstStep_p4_spaceFacts`), so the spanner
parameters agree (`asmFirstStepSpace_le_poly_std_at`). For `hSp4` the room before the step
(`AsmFsPre`) gives `A.h + space X < 2 ^ w`. For `hSpG` the post of Phase 4 bounds its value by
`hEnd₃` plus the cells of Phase 4.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

public section

/-- **`asmFirstStepSpace_le_poly_std` at other spanners**: the spanners `S6` may have any cap
equal to the cap of the side record, and the parameters `SP` may be any parameters equal to those
of the side record. -/
theorem asmFirstStepSpace_le_poly_std_at
    {depth w P L capExp limbMul : ℕ} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {impl : SparsifyImpl} {C_sp : ℝ} (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    {Ψ : BundleTreeState depth → ℕ} {c₀ : ℕ}
    {b k M N vCap eCap words editWords nDel nSp nU nEd lo hi : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    {x : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).τ}
    {mem mem₃ : ℕ → ℕ} {newComps : List (ℕ × ℕ)}
    {cap : ℕ} {S6 : BucketSpannerState cap} {SP : DSParams} {tasks : List SpanUpdTask}
    (hcap : cap = x.xRest.cap) (hSP : SP = asmBrSP impl w depth x.xRest)
    (hrep : (asmBrFullRep (depth := depth) TR
      (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB)
      impl w P L capExp limbMul Ψ).rep b ⟨tr, ord, vCap, eCap⟩ x mem)
    (hM : tr.m₀ = M) (hN : tr.n₀ = N) (hdepth1 : 1 ≤ depth)
    (hdepth : depth ≤ Expander.chosenL ((M + N) ^ 2))
    (hGE : ∀ e ∈ tr.cs.G.E, e < eCap)
    (hNC_len : newComps.length ≤ words)
    (hSum : newCompsBucketSum tr x.xRest.comps newComps ≤ x.xRest.slotCap)
    (hnDel : nDel ≤ words)
    (htasks_len : tasks.length ≤ x.xRest.slotCap)
    (hnew_len : hi - lo ≤ x.xRest.slotCap)
    (hnSp : nSp ≤ vCap) (hnU : nU ≤ words) (hnEd : nEd ≤ editWords)
    (hS6_valid : ∀ (j : Fin cap) (d : DSHist), S6 j = some d → P4HistValid SP d)
    (htasks_valid : ∀ t ∈ tasks, P4TaskValid SP S6 mem₃ t ∧
      t.W ≤ asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel) :
    c₀ + 6 + asmFirstScanBatchSpace vCap eCap words +
      newActTotalSpace tourBundleSpec 1 impl w x.xRest tr ord newComps +
      asmFirstPhase3Space x.xRest.slotCap vCap eCap words editWords nDel +
      p4WsSize eCap + (tasks.map (p4TaskSpace SP S6 mem₃)).sum +
      rangeCost (p4NewSpace SP (p4SpanAfter SP S6 mem₃ tasks)) lo hi +
      asmFirstPhase4Room vCap eCap nSp nU nEd 1 1 ≤
      asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp
        (M + N + k + vCap + eCap + L + depth + words + editWords) := by
  subst hcap hSP
  exact asmFirstStepSpace_le_poly_std hC hγ hrep hM hN hdepth1 hdepth hGE hNC_len hSum hnDel
    htasks_len hnew_len hnSp hnU hnEd hS6_valid htasks_valid

set_option maxHeartbeats 1000000 in
/-- **The end of Phase 3 plus the cells of Phase 4 is at most `A.h + space X`**, for the root
query of space `1`. The premise `hOut` is the first part of `AsmFsP4Open`. -/
theorem asmFirstStep_p4_end_le {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w c₀ : ℕ} {C_sp : ℝ} {Ψ : BundleTreeState depth → ℕ}
    {p : Program} {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} (hq : hRoot.querySpace = 1)
    (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ)))
    (A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth)
    (st₁ : State) (c₁ : ℕ) (st₂ : State) (c₂ : ℕ) (st₃ : State) (c₃ hEnd₂ : ℕ)
    (y' : AsmBrSide scProgB5 depth) (tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ)
    (hEnd₃ : ℕ) (tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ)
    (splitPtr outDescPtr : ℕ) (mk' : Finset End) (Mset : Finset ℕ) (Ys : List (List End))
    (touched : List ℕ)
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ
      (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp) A)
    (hQ₃ : AsmFsQ₃At tourBundleSpec impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p
      hRoot bBun bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched)
    (hOut : AsmFirstBunStepOut (asmBrSP impl w depth y') y'.cap y'.spanS (outDescPtr + 1) hEnd₃
      (p4TasksOf st₃.mem (outDescPtr + 1) touched.length) st₃.mem) :
    hEnd₃ + p4WsSize A.x.eCap +
      ((p4TasksOf st₃.mem (outDescPtr + 1) touched.length).map
        (p4TaskSpace (asmBrSP impl w depth y') y'.spanS st₃.mem)).sum +
      rangeCost (p4NewSpace (asmBrSP impl w depth y')
        (p4SpanAfter (asmBrSP impl w depth y') y'.spanS st₃.mem
          (p4TasksOf st₃.mem (outDescPtr + 1) touched.length)))
        A.x.xRest.slots.length
        (A.x.xRest.slots.length + newCompsBucketSum A.tr A.x.xRest.comps
          (A.newComps A.x.xRest.cmpH A.x.xRest.comps)) +
      asmFirstPhase4Room A.x.vCap A.x.eCap (canonSplitList A.tr.cs A.U).length A.U.length
        A.ed.length 1 1 ≤
      A.h + asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp
        (A.M + A.N + A.k + A.x.vCap + A.x.eCap + L + depth + A.words + A.editWords) := by
  obtain ⟨hSlot, hTasks, hTouch, hEnd₃le, hcap, hspV, hspE, hmMax, hsplitB⟩ :=
    asmFirstStep_p4_spaceFacts A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr
      outDescPtr mk' Mset Ys touched hA hQ₃ hOut
  obtain ⟨hGE, hNC, hSum, hDel⟩ := asmFirstStep_prefix_facts A hA
  rw [hq] at hEnd₃le
  have hA' := hA
  unfold AsmFsPre AsmFsPreRaw at hA'
  obtain ⟨hM, hN, hd1, -, -, -, -, -, -, hR, hFacts, hBat, hU, -, hEdAt, hOB, -, -, -, -, -,
    -, -, -, -, -, -, -, -, hdepth⟩ := hA'
  obtain ⟨-, ⟨C_lsst, ℓ₀, hI, -, -⟩, -⟩ := asmBrModelFacts_of_rep hR
  have hRoots : ∀ r ∈ (compLSFBatch A.tr.cs A.U).RF.R, r < A.x.vCap :=
    asmBr_newRoots_lt (fun _ => canonicalSparsify impl) hFacts
  have hnSp : (canonSplitList A.tr.cs A.U).length ≤ A.x.vCap :=
    asmFirstCanonSplitList_length_le_vCap hI hU hOB hRoots
  have hUW : 2 * A.U.length ≤ A.words - 1 := batchBodyAt_len_le hBat.1.2.2
  have hnEd := ordEditsAt_two_len hEdAt
  have hSP : asmBrSP impl w depth y' = asmBrSP impl w depth A.x.xRest := by
    simp only [asmBrSP, hspV, hspE, hmMax, hsplitB]
  have hlen := p4TasksOf_length st₃.mem (outDescPtr + 1) touched.length
  have hle := asmFirstStepSpace_le_poly_std_at (c₀ := c₀) (k := A.k) (editWords := A.editWords)
    (nU := A.U.length) (nEd := A.ed.length) (mem₃ := st₃.mem)
    (S6 := y'.spanS) (SP := asmBrSP impl w depth y')
    (tasks := p4TasksOf st₃.mem (outDescPtr + 1) touched.length)
    (lo := A.x.xRest.slots.length)
    (hi := A.x.xRest.slots.length + newCompsBucketSum A.tr A.x.xRest.comps
      (A.newComps A.x.xRest.cmpH A.x.xRest.comps))
    hC hγ hcap hSP hR hM hN hd1 hdepth hGE hNC hSum hDel (by omega)
    (by simp only [AsmFsArgs.newComps]; omega) hnSp
    (by omega) (by omega) (fun j d hjd => (hSlot j d hjd).1) hTasks
  omega

set_option maxHeartbeats 1000000 in
/-- **The room of Phase 4** (`hSp4` of the pieces), for the queries of space `1`. -/
theorem asmFirstStep_hSp4_std {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w c₀ : ℕ} {C_sp : ℝ} {Ψ : BundleTreeState depth → ℕ}
    {p : Program} {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} (hq : hRoot.querySpace = 1)
    {qE : ℕ} (hqE : qE = 1) (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ))) :
    ∀ A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr mk'
        Mset Ys touched,
      AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ
        (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp) A →
      AsmFsQ₃At tourBundleSpec impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot
        bBun bTourStep fDelTriples fBuildGroups A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃
        tx_pot' splitPtr outDescPtr mk' Mset Ys touched →
      AsmFsP4Room w (asmBrSP impl w depth y') y'.spanS st₃.mem hEnd₃ A.x.vCap A.x.eCap
        (outDescPtr + 1) touched.length A.x.xRest.slots.length
        (A.x.xRest.slots.length + newCompsBucketSum A.tr A.x.xRest.comps
          (A.newComps A.x.xRest.cmpH A.x.xRest.comps))
        (canonSplitList A.tr.cs A.U).length A.U.length A.ed.length qE hRoot.querySpace := by
  intro A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr mk'
    Mset Ys touched hA hQ₃
  have hOut := (asmFirstStep_hOpen hRoot A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot'
    splitPtr outDescPtr mk' Mset Ys touched hA hQ₃).1
  have hle := asmFirstStep_p4_end_le hq hC hγ A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃
    tx_pot' splitPtr outDescPtr mk' Mset Ys touched hA hQ₃ hOut
  have hroom := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  unfold AsmFsP4Room
  rw [hq, hqE]
  omega

set_option maxHeartbeats 1000000 in
/-- **The bound of the last result** (`hSpG` of the pieces), for the queries of space `1`: the
value that Phase 4 returns is at most `A.h + space X`, by its post and
`asmFirstStep_p4_end_le`. -/
theorem asmFirstStep_hSpG_std {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w c₀ : ℕ} {C_sp : ℝ} {Ψ : BundleTreeState depth → ℕ}
    {p : Program} {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    (hq : hRoot.querySpace = 1) (hqE : K.HE.querySpace = 1) (hC : 0 < C_sp)
    (hγ : ∀ m, impl.γ_ℓ m ≤ Real.exp (C_sp * Real.log ((m : ℝ) + 2) ^ (7 / 8 : ℝ))) :
    AsmFsSpaceGoal tourBundleSpec impl P L capExp limbMul wordExp w Ψ fVertRoot fInitOne
      fInitSpan p hRoot bBun bTourStep fDelTriples fBuildGroups K
      (asmFirstStepSpaceFnStd c₀ impl.cw capExp C_sp) := by
  intro A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot' splitPtr outDescPtr
    mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀ hA hQ₄
  obtain ⟨hQ₃, hP4⟩ := hQ₄
  have hOut := (asmFirstStep_hOpen hRoot A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃ tx_pot'
    splitPtr outDescPtr mk' Mset Ys touched hA hQ₃).1
  have hle := asmFirstStep_p4_end_le hq hC hγ A st₁ c₁ st₂ c₂ st₃ c₃ hEnd₂ y' tx1 lazyE hEnd₃
    tx_pot' splitPtr outDescPtr mk' Mset Ys touched hA hQ₃ hOut
  have hval := hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  rw [hq, hqE] at hval
  obtain ⟨b, batch, words, edits, editWords, chg, spPtr, h, k, M, N, n, tr, ord, x, U, ed, c,
    mem, pos, ω⟩ := A
  have hv := hA.2.2.2.2.2.2.2.2.2.1.2.1
  have he := hA.2.2.2.2.2.2.2.2.2.1.2.2.1
  dsimp only at hle hval hv he ⊢
  simp only [hv, he] at hval
  omega

end

end MinCostFlow.SparseCore.Program
