module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepCostGoal

import MinCostFlow.SparseCore.Program.AssemblyFirstStepPostTour
import MinCostFlow.SparseCore.Program.AssemblyFirstStepGlue2
import Mathlib.Tactic

/-!
# Potential telescoping across the four phases of the first step (`AssemblyFsCostPot`)

Identifies every term of the branch potential `R.phi` before (`A.mem`) and after
(`mem' := Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)`) the four phases of the first step:

* `asmFsCost_places`: the heap inequalities `A.h + 6 ≤ hScan ≤ hEnd₂ ≤ hEnd₃ ≤ o₄.value` and the
  disjointness of the final tour and bundle-table footprints from `[A.h, A.h + 6)`.
* `asmFsCost_tour_phi`: the old tour potential at `A.mem` equals that of `tx₀` at `st₁.mem`, and
  the new tour potential at `mem'` equals that of `tx'` at `st₄.mem`.
* `asmFsCost_bun_phi`: the old bundle-table potential at `A.mem` equals that at `st₁.mem`, and
  the new bundle-table potential at `mem'` equals that of `y'` at `st₃.mem`.
* `asmFsCost_span_phi`: `bucketPhi` equals `specPhi` before Phase 2, after Phase 2, and after
  Phase 4, with identical spanner parameters `asmBrSP` and log factor `bundleLogFactor A.M A.N`.
* `asmFsCost_phi_eq`: puts all five parts of `R.phi` together so the readout potential cancels and
  the remaining four terms match the potentials appearing in the Phase 2, 3, and 4 cost bounds.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart MinCostFlow.SparseCore.Program.Read

/-- The tour family of `scProg`. -/
local notation "TRc" => asmTourRepWithPot tourAsmRep (bundleScanPotMul tourBundleSpec)

public section

/-- **Heap places and footprint separation** from `AsmFsPre` and `AsmFsQ₄At`:
`A.h + 6 ≤ hScan ≤ hEnd₂`, `hEnd₂ + 2 ≤ hEnd₃ ≤ o₄.value`, every cell of the tour `tx'` and of
the bundle table `y'.xBun` lies outside `[A.h, A.h + 6)`, and the bundle table `y'.xBun` is kept
by Phase 4's frame (`< hEnd₃`, disjoint from `y'.spanH`, `A.x.embH`, `tx_pot'`). -/
theorem asmFsCost_places {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {st₂ : State} {c₂ : ℕ} {st₃ : State} {c₃ : ℕ}
    {o₄ : Outcome} {st₄ : State} {c₄ : ℕ}
    {hEnd₂ : ℕ} {y' : AsmBrSide scProgB5 depth} {tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ}
    {lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ} {hEnd₃ : ℕ}
    {tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {splitPtr outDescPtr : ℕ}
    {mk' : Finset End} {Mset : Finset ℕ} {Ys : List (List End)} {touched : List ℕ}
    {qs : List (SpanUpdTask × P4TaskOut)} {ns : List (ℕ × List ℕ)}
    {x' : BucketSpannerMeta depth y'.cap} {yE : EmbConc}
    {tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {Ld Li Lr T₀ : List ℕ}
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ : AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀) :
    A.h + 6 ≤ hEnd₂ ∧ hEnd₂ + 2 ≤ hEnd₃ ∧ hEnd₃ ≤ o₄.value ∧
    (∀ a, (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).foot A.x.tourH tx' a →
      a < A.h ∨ A.h + 6 ≤ a) ∧
    (∀ a, (scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).foot y'.bunH y'.xBun a →
      a < hEnd₃ ∧ ¬ bucketFoot y'.spanH y'.xSpan a ∧
      ¬ embFoot A.x.xRest.eCap5 A.x.embH A.x.yEmb a ∧
      ¬ (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).foot A.x.tourH tx_pot' a ∧
      (a < A.h ∨ A.h + 6 ≤ a)) := by
  obtain ⟨hQ₃, hP4⟩ := hQ
  obtain ⟨_, tx₀, hTx₀, hP2, hP3⟩ := hQ₃
  have hR := hA.2.2.2.2.2.2.2.2.2.1
  have hfoot := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv5 : A.x.xRest.vCap5 = A.x.vCap := hR.2.1
  have he5 : A.x.xRest.eCap5 = A.x.eCap := hR.2.2.1
  have hDisj : AsmBrDisjoint (asmBrSideRep scProgB5 impl w depth L capExp limbMul Ψ) A.b A.x :=
    hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hfootT0 : ∀ a, (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).foot A.x.tourH tx₀ a → a < A.h := by
    intro a ha
    have ha' : (TRc A.x.vCap A.x.eCap).foot A.x.tourH A.x.xTour a :=
      (tourRep_heq hv5 he5 hTx₀ A.x.tourH).2.1 a |>.mp ha
    exact hfoot a ⟨4, by decide, ha'⟩
  have hfootS0 : ∀ a, asmSdFoot A.x.restH A.x.xRest a → a < A.h :=
    fun a ha => hfoot a ⟨5, by decide, ha⟩
  have hfootE0 : ∀ a, embFoot A.x.xRest.eCap5 A.x.embH A.x.yEmb a → a < A.h := by
    intro a ha; rw [he5] at ha; exact hfoot a ⟨2, by decide, ha⟩
  have hdisjSE : ∀ a, asmSdFoot A.x.restH A.x.xRest a →
      ¬ embFoot A.x.xRest.eCap5 A.x.embH A.x.yEmb a := by
    intro a hs he; rw [he5] at he
    exact hDisj 5 (by decide) 2 (by decide) (by decide) a hs he
  -- Extract places from Phase 2, Phase 3, Phase 4 posts
  have hP2_disj : ∀ i < 4, ∀ j < 4, i ≠ j → ∀ a,
      asmSdPart A.x.restH y' i a → ¬ asmSdPart A.x.restH y' j a :=
    hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP2_disjT : ∀ a, asmSdFoot A.x.restH y' a →
      ¬ (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).foot A.x.tourH tx1 a :=
    hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP2_lo : A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words +
      2 * (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length ≤ hEnd₂ :=
    hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP2_ftS : ∀ a, asmSdFoot A.x.restH y' a → asmSdFoot A.x.restH A.x.xRest a ∨
      (A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words +
        2 * (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length ≤ a ∧ a < hEnd₂) :=
    hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP2_ftT : ∀ a, (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).foot A.x.tourH tx1 a →
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).foot A.x.tourH tx₀ a ∨
      (A.h + 6 + asmFirstScanBatchSpace A.x.vCap A.x.eCap A.words +
        2 * (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length ≤ a ∧ a < hEnd₂) :=
    hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP3_lo : hEnd₂ + 2 ≤ hEnd₃ :=
    hP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP3_ftT : ∀ a, (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).foot A.x.tourH tx_pot' a →
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).foot A.x.tourH tx1 a ∨
      (hEnd₂ + 2 ≤ a ∧ a < hEnd₃) :=
    hP3.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP4_lo : hEnd₃ ≤ o₄.value :=
    hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hP4_ftT : ∀ a, (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).foot A.x.tourH tx' a →
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).foot A.x.tourH tx_pot' a ∨
      (hEnd₃ ≤ a ∧ a < o₄.value) :=
    hP4.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  refine ⟨by omega, hP3_lo, hP4_lo, ?_, ?_⟩
  · intro a ha
    rcases hP4_ftT a ha with h3 | ⟨hlo, _⟩
    · rcases hP3_ftT a h3 with h2 | ⟨hlo, _⟩
      · rcases hP2_ftT a h2 with h1 | ⟨hlo, _⟩
        · exact Or.inl (hfootT0 a h1)
        · exact Or.inr (by omega)
      · exact Or.inr (by omega)
    · exact Or.inr (by omega)
  · intro a ha
    have haSd : asmSdFoot A.x.restH y' a := ⟨1, by decide, ha⟩
    have ha_lt_h2 : a < hEnd₂ := by
      rcases hP2_ftS a haSd with h0 | ⟨_, hhi⟩
      · have := hfootS0 a h0; omega
      · exact hhi
    have ha_out : a < A.h ∨ A.h + 6 ≤ a := by
      rcases hP2_ftS a haSd with h0 | ⟨hlo, _⟩
      · exact Or.inl (hfootS0 a h0)
      · exact Or.inr (by omega)
    refine ⟨by omega,
      fun hsp => hP2_disj 1 (by decide) 2 (by decide) (by decide) a ha hsp,
      fun he => by
        rcases hP2_ftS a haSd with h0 | ⟨hlo, _⟩
        · exact hdisjSE a h0 he
        · have := hfootE0 a he; omega,
      fun ht => by
        rcases hP3_ftT a ht with ht1 | ⟨hlo, _⟩
        · exact hP2_disjT a haSd ht1
        · omega,
      ha_out⟩

/-- **Tour potential at start and end**:
1. The old branch's tour potential in `A.mem` equals the Phase 2 input tour potential of `tx₀` in
   `st₁.mem`;
2. The new branch's tour potential in `mem' = Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)`
   equals the Phase 4 output tour potential of `tx'` in `st₄.mem`. -/
theorem asmFsCost_tour_phi {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {st₂ : State} {c₂ : ℕ} {st₃ : State} {c₃ : ℕ}
    {o₄ : Outcome} {st₄ : State} {c₄ : ℕ}
    {hEnd₂ : ℕ} {y' : AsmBrSide scProgB5 depth} {tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ}
    {lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ} {hEnd₃ : ℕ}
    {tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {splitPtr outDescPtr : ℕ}
    {mk' : Finset End} {Mset : Finset ℕ} {Ys : List (List End)} {touched : List ℕ}
    {qs : List (SpanUpdTask × P4TaskOut)} {ns : List (ℕ × List ℕ)}
    {x' : BucketSpannerMeta depth y'.cap} {yE : EmbConc}
    {tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {Ld Li Lr T₀ : List ℕ}
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ : AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀)
    {tx₀ : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} (hTx₀ : HEq tx₀ A.x.xTour)
    {xTour : (TRc A.x.vCap A.x.eCap).τ} (hTx' : HEq xTour tx') :
    (TRc A.x.vCap A.x.eCap).phi A.x.tourH A.x.xTour A.mem =
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx₀ st₁.mem ∧
    (TRc A.x.vCap A.x.eCap).phi A.x.tourH xTour
        (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)) =
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx' st₄.mem := by
  have hR := hA.2.2.2.2.2.2.2.2.2.1
  have hfoot := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hv5 : A.x.xRest.vCap5 = A.x.vCap := hR.2.1
  have he5 : A.x.xRest.eCap5 = A.x.eCap := hR.2.2.1
  have hDisj : AsmBrDisjoint (asmBrSideRep scProgB5 impl w depth L capExp limbMul Ψ) A.b A.x :=
    hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hTRloc : ∀ v e, (TRc v e).Local := fun v e =>
    asmTourRepWithPot_local tourAsmRep_local (bundleScanPotMul tourBundleSpec) v e
  have hScanM := hQ.1.1.1
  have hPl := asmFsCost_places hA hQ
  constructor
  · have h1 := (tourRep_heq hv5 he5 hTx₀ A.x.tourH).2.2 A.mem
    have h2 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx₀ A.mem =
        (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx₀ st₁.mem := by
      refine (hTRloc A.x.xRest.vCap5 A.x.xRest.eCap5 A.x.tourH ⟨A.ord, A.tr.cs.RF, A.x.sTour.marked⟩
        tx₀ A.mem st₁.mem ?_).2
      intro a ha
      have ha' : (TRc A.x.vCap A.x.eCap).foot A.x.tourH A.x.xTour a :=
        (tourRep_heq hv5 he5 hTx₀ A.x.tourH).2.1 a |>.mp ha
      have ha_lt : a < A.h := hfoot a ⟨4, by decide, ha'⟩
      have hnsd : ¬ asmSdFoot A.x.restH A.x.xRest a :=
        fun hs => hDisj 5 (by decide) 4 (by decide) (by decide) a hs ha'
      refine (asmFirstStep_scan_frame hScanM a (by omega) ?_ ?_).symm
      · intro v hv heq; subst heq
        exact hnsd ⟨3, by decide, Or.inr ⟨0, by omega, by omega⟩⟩
      · intro c hc heq; subst heq
        exact hnsd ⟨3, by decide, Or.inr ⟨2, by omega, by omega⟩⟩
    exact h1.symm.trans h2
  · have h1 := (tourRep_heq hv5.symm he5.symm hTx' A.x.tourH).2.2
      (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂))
    have h2 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx'
          (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)) =
        (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx' st₄.mem := by
      refine (hTRloc A.x.xRest.vCap5 A.x.xRest.eCap5 A.x.tourH
        ⟨applyOrdEdits A.ord A.ed, (compLSFBatch A.tr.cs A.U).RF, mk'⟩ tx'
        (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)) st₄.mem ?_).2
      intro a ha
      have hne : a ≠ A.h + 1 := by
        rcases hPl.2.2.2.1 a ha with hlt | hge <;> omega
      exact Function.update_of_ne hne _ _
    exact h1.trans h2

/-- **Bundle-table potential at start and end**:
1. The old bundle-table potential in `A.mem` equals that in `st₁.mem` (Phase 1 keeps part 1 of the
   side record);
2. The new bundle-table potential in `mem' = Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)`
   equals that of `y'` in `st₃.mem` (Phase 4 and the driver store keep `y'.xBun`'s footprint). -/
theorem asmFsCost_bun_phi {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {st₂ : State} {c₂ : ℕ} {st₃ : State} {c₃ : ℕ}
    {o₄ : Outcome} {st₄ : State} {c₄ : ℕ}
    {hEnd₂ : ℕ} {y' : AsmBrSide scProgB5 depth} {tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ}
    {lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ} {hEnd₃ : ℕ}
    {tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {splitPtr outDescPtr : ℕ}
    {mk' : Finset End} {Mset : Finset ℕ} {Ys : List (List End)} {touched : List ℕ}
    {qs : List (SpanUpdTask × P4TaskOut)} {ns : List (ℕ × List ℕ)}
    {x' : BucketSpannerMeta depth y'.cap} {yE : EmbConc}
    {tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {Ld Li Lr T₀ : List ℕ}
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ : AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀) :
    (scProgB5 A.x.xRest.kB A.x.xRest.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5).phi
        A.x.xRest.bunH A.x.xRest.xBun A.mem =
      (scProgB5 A.x.xRest.kB A.x.xRest.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5).phi
        A.x.xRest.bunH A.x.xRest.xBun st₁.mem ∧
    (scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun
        (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)) =
      (scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun st₃.mem := by
  have hR := hA.2.2.2.2.2.2.2.2.2.1
  have hv5 : A.x.xRest.vCap5 = A.x.vCap := hR.2.1
  have hfoot := hA.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSide := hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSdDisj : ∀ i < 4, ∀ j < 4, i ≠ j → ∀ a,
      asmSdPart A.x.restH A.x.xRest i a → ¬ asmSdPart A.x.restH A.x.xRest j a :=
    hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hScanM := hQ.1.1.1
  have hP4_fr := hQ.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hPl := asmFsCost_places hA hQ
  constructor
  · refine (bunTableHeadroomRep_local A.x.xRest.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5
      A.x.xRest.kB A.x.xRest.bunH A.x.xRest.bunS A.x.xRest.xBun A.mem st₁.mem ?_).2
    intro a ha
    have ha_lt : a < A.h := hfoot a ⟨5, by decide, ⟨1, by decide, ha⟩⟩
    refine (asmFirstStep_scan_frame hScanM a (by omega) ?_ ?_).symm
    · intro v hv heq; subst heq
      exact hSdDisj 1 (by decide) 3 (by decide) (by decide) _ ha
        (Or.inr ⟨0, by omega, by omega⟩)
    · intro c hc heq; subst heq
      exact hSdDisj 1 (by decide) 3 (by decide) (by decide) _ ha
        (Or.inr ⟨2, by omega, by omega⟩)
  · refine (bunTableHeadroomRep_local y'.slotCap y'.vCap5 y'.eCap5 y'.kB y'.bunH y'.bunS y'.xBun
      (Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)) st₃.mem ?_).2
    intro a ha
    obtain ⟨hlt, hnsp, hne, hnt, hout⟩ := hPl.2.2.2.2 a ha
    have hne1 : a ≠ A.h + 1 := by rcases hout with h1 | h2 <;> omega
    rw [Function.update_of_ne hne1]
    exact hP4_fr a hlt hnsp hne hnt hout

/-- **Spanner parameters, log factor, and `bucketPhi = specPhi`** at all three checkpoints:
before Phase 2 (`A.x.xRest`), after Phase 2 (`y'`), and after Phase 4 (`asmFsSideAfter`). -/
theorem asmFsCost_span_phi {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {st₂ : State} {c₂ : ℕ} {st₃ : State} {c₃ : ℕ}
    {o₄ : Outcome} {st₄ : State} {c₄ : ℕ}
    {hEnd₂ : ℕ} {y' : AsmBrSide scProgB5 depth} {tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ}
    {lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ} {hEnd₃ : ℕ}
    {tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {splitPtr outDescPtr : ℕ}
    {mk' : Finset End} {Mset : Finset ℕ} {Ys : List (List End)} {touched : List ℕ}
    {qs : List (SpanUpdTask × P4TaskOut)} {ns : List (ℕ × List ℕ)}
    {x' : BucketSpannerMeta depth y'.cap} {yE : EmbConc}
    {tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {Ld Li Lr T₀ : List ℕ}
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ : AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀) :
    let yAfter := asmFsSideAfter impl w Ψ A.tr A.U A.ord A.ed y' st₃.mem outDescPtr
      touched.length x'
    let P_sp := asmBrSP impl w depth y'
    asmBrSP impl w depth A.x.xRest = P_sp ∧
    asmBrSP impl w depth yAfter = P_sp ∧
    A.x.xRest.lgFac = bundleLogFactor A.M A.N ∧
    y'.lgFac = bundleLogFactor A.M A.N ∧
    yAfter.lgFac = bundleLogFactor A.M A.N ∧
    bucketPhi (asmBrSP impl w depth A.x.xRest) A.x.xRest.xSpan = specPhi P_sp A.x.xRest.spanS ∧
    bucketPhi P_sp y'.xSpan = specPhi P_sp y'.spanS ∧
    bucketPhi (asmBrSP impl w depth yAfter) yAfter.xSpan =
      specPhi P_sp (p4SpanAfter P_sp y'.spanS st₃.mem
        (p4TasksOf st₃.mem (outDescPtr + 1) touched.length)) := by
  intro yAfter P_sp
  have hM0 : A.tr.m₀ = A.M := hA.1
  have hN0 : A.tr.n₀ = A.N := hA.2.1
  have hR := hA.2.2.2.2.2.2.2.2.2.1
  have hSide := hR.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSpanRep0 := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMod0 := hSide.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hLg0 : A.x.xRest.lgFac = bundleLogFactor A.M A.N := by
    rw [← hM0, ← hN0]; exact hMod0.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  obtain ⟨_, _, _, hP2, _⟩ := hQ.1
  have hsb : y'.splitB = A.x.xRest.splitB := hP2.2.2.2.2.2.2.2.2.2.1
  have hspV : y'.spV = A.x.xRest.spV := hP2.2.2.2.2.2.2.2.2.2.2.1
  have hspE : y'.spE = A.x.xRest.spE := hP2.2.2.2.2.2.2.2.2.2.2.2.1
  have hmMax : y'.mMax = A.x.xRest.mMax := hP2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hlg' : y'.lgFac = A.x.xRest.lgFac :=
    hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSpanRep2 := hP2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hSpanRep4 := hQ.2.2.2.2.2.1
  have hSP0 : asmBrSP impl w depth A.x.xRest = P_sp := by
    simp only [P_sp, asmBrSP, hsb, hspV, hspE, hmMax]
  have hSPa : asmBrSP impl w depth yAfter = P_sp := rfl
  refine ⟨hSP0, hSPa, hLg0, hlg'.trans hLg0, hlg'.trans hLg0, ?_, ?_, ?_⟩
  · have h : bucketPhi (asmBrSP impl w depth A.x.xRest) A.x.xRest.xSpan =
        specPhi (asmBrSP impl w depth A.x.xRest) A.x.xRest.spanS := bucketPhi_eq_specPhi hSpanRep0
    exact h.trans (congrArg (fun Q => specPhi Q A.x.xRest.spanS) hSP0)
  · exact bucketPhi_eq_specPhi hSpanRep2
  · exact bucketPhi_eq_specPhi hSpanRep4

/-- **Full branch-potential decomposition** before and after the step:
cancels `readPotMul * treePot` and rewrites every other potential term of `R.phi` in the exact
form appearing in the Phase 2, Phase 3, and Phase 4 cost bounds. -/
theorem asmFsCost_phi_eq {TS : BundleTourSpec} {depth : ℕ} {impl : SparsifyImpl}
    {P L capExp limbMul wordExp w : ℕ} {Ψ : BundleTreeState depth → ℕ} {p : Program}
    {fVertRoot fInitOne fInitSpan bBun bTourStep fDelTriples fBuildGroups : ℕ}
    {hRoot : AsmFirstTourRootAt TRc w p fVertRoot} {K : AsmFirstP4Code TRc w impl p fVertRoot}
    {space : ℕ → ℕ}
    {A : AsmFsArgs (asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ).τ
      depth}
    {st₁ : State} {c₁ : ℕ} {st₂ : State} {c₂ : ℕ} {st₃ : State} {c₃ : ℕ}
    {o₄ : Outcome} {st₄ : State} {c₄ : ℕ}
    {hEnd₂ : ℕ} {y' : AsmBrSide scProgB5 depth} {tx1 : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ}
    {lazyE : Fin (A.newComps A.x.xRest.cmpH A.x.xRest.comps).length → List ℕ} {hEnd₃ : ℕ}
    {tx_pot' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {splitPtr outDescPtr : ℕ}
    {mk' : Finset End} {Mset : Finset ℕ} {Ys : List (List End)} {touched : List ℕ}
    {qs : List (SpanUpdTask × P4TaskOut)} {ns : List (ℕ × List ℕ)}
    {x' : BucketSpannerMeta depth y'.cap} {yE : EmbConc}
    {tx' : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} {Ld Li Lr T₀ : List ℕ}
    (hA : AsmFsPre TRc scProgB5 impl P L capExp limbMul wordExp w Ψ space A)
    (hQ : AsmFsQ₄At TS impl P L capExp limbMul w Ψ fVertRoot fInitOne fInitSpan p hRoot bBun
      bTourStep fDelTriples fBuildGroups K A st₁ c₁ st₂ c₂ st₃ c₃ o₄ st₄ c₄ hEnd₂ y' tx1 lazyE
      hEnd₃ tx_pot' splitPtr outDescPtr mk' Mset Ys touched qs ns x' yE tx' Ld Li Lr T₀)
    {tx₀ : (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).τ} (hTx₀ : HEq tx₀ A.x.xTour)
    {xTour : (TRc A.x.vCap A.x.eCap).τ} (hTx' : HEq xTour tx')
    (yEmb : EmbConc) (sTour : OutTourAbs) :
    let R := asmBrFullRep (depth := depth) TRc scProgB5 impl w P L capExp limbMul Ψ
    let yAfter := asmFsSideAfter impl w Ψ A.tr A.U A.ord A.ed y' st₃.mem outDescPtr
      touched.length x'
    let x₁ := A.x.afterCore yEmb sTour xTour yAfter
    let mem' := Function.update st₄.mem (A.h + 1) (st₃.mem hEnd₂)
    let P_sp := asmBrSP impl w depth y'
    let sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
    let info := stepBundleTree sp A.tr A.U A.ord (applyOrdEdits A.ord A.ed)
    R.phi A.b A.x A.mem =
      readPotMul * treePot A.x.yRead.view.G A.x.yRead.view.lsf.T +
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx₀ st₁.mem +
      ((scProgB5 A.x.xRest.kB A.x.xRest.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5).phi
        A.x.xRest.bunH A.x.xRest.xBun st₁.mem +
       320 * (capExp + 1) * bundleLogFactor A.M A.N * specPhi P_sp A.x.xRest.spanS +
       300 * Ψ A.tr) ∧
    R.phi A.b x₁ mem' =
      readPotMul * treePot A.x.yRead.view.G A.x.yRead.view.lsf.T +
      (TRc A.x.xRest.vCap5 A.x.xRest.eCap5).phi A.x.tourH tx' st₄.mem +
      ((scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun st₃.mem +
       320 * (capExp + 1) * bundleLogFactor A.M A.N *
         specPhi P_sp (p4SpanAfter P_sp y'.spanS st₃.mem
           (p4TasksOf st₃.mem (outDescPtr + 1) touched.length)) +
       300 * Ψ info.state) := by
  intro R yAfter x₁ mem' P_sp sp info
  obtain ⟨hT0, hT1⟩ := asmFsCost_tour_phi hA hQ hTx₀ hTx'
  obtain ⟨hB0, hB1⟩ := asmFsCost_bun_phi hA hQ
  obtain ⟨_, _, hLg0, _, hLga, hS0, _, hSa⟩ := asmFsCost_span_phi hA hQ
  have hMod0 := hA.2.2.2.2.2.2.2.2.2.1.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hWP0 : A.x.xRest.walkPot = Ψ A.tr := hMod0.2.2.2.2.2.2.2.2.2.2.2.2.1
  constructor
  · change readPotMul * treePot A.x.yRead.view.G A.x.yRead.view.lsf.T +
      (TRc A.x.vCap A.x.eCap).phi A.x.tourH A.x.xTour A.mem +
      ((scProgB5 A.x.xRest.kB A.x.xRest.slotCap A.x.xRest.vCap5 A.x.xRest.eCap5).phi
          A.x.xRest.bunH A.x.xRest.xBun A.mem +
        320 * (capExp + 1) * A.x.xRest.lgFac *
          bucketPhi (asmBrSP impl w depth A.x.xRest) A.x.xRest.xSpan +
        300 * A.x.xRest.walkPot) = _
    rw [hT0, hB0, hLg0, hS0, hWP0]
  · change readPotMul * treePot A.x.yRead.view.G A.x.yRead.view.lsf.T +
      (TRc A.x.vCap A.x.eCap).phi A.x.tourH xTour mem' +
      ((scProgB5 y'.kB y'.slotCap y'.vCap5 y'.eCap5).phi y'.bunH y'.xBun mem' +
        320 * (capExp + 1) * yAfter.lgFac *
          bucketPhi (asmBrSP impl w depth yAfter) yAfter.xSpan +
        300 * Ψ info.state) = _
    rw [hT1, hB1, hLga, hSa]

end

end MinCostFlow.SparseCore.Program
