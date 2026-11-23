module

public import MinCostFlow.SparseCore.Program.AssemblyBranchTour
public import MinCostFlow.SparseCore.Program.AssemblyBranchOrd
public import MinCostFlow.SparseCore.Program.AssemblyBranchRestartIface
public import MinCostFlow.SparseCore.Program.AssemblyBranchBunValue
public import MinCostFlow.SparseCore.Program.BundlePotBridge
public import MinCostFlow.SparseCore.Program.BundleStepDefs
public import MinCostFlow.SparseCore.Program.BundleStepScanAmort
public import MinCostFlow.SparseCore.Program.BundleCapHeadroom

import MinCostFlow.Bundle.CoreCongr

/-!
# Tour potential wrapper and bundle capacity headroom invariant (`AssemblyFirstTourPot`)

Provides two foundations needed to connect P2's tour and P5's bundle manager into the branch
representation (`AssemblyBranchFull`) and first phases (`AsmBrCoreStepAt`, `AsmBrCoreInitAt`):

1. **Tour-potential wrapper (`asmTourRepWithPot`)**:
   - Proves `tourCordOK_unique`: the core rotation lists `cord` matching `(ord, rf)` under
     `TourCordOK ord rf cord` are uniquely determined by `(ord, rf)`, so `tourPotOfAbs a` agrees
     with `tourPot rf.R cord`.
   - Defines `asmTourRepWithPot TR cPot`, which adds `cPot * tourPotOfAbs a` into the tour's
     potential without changing memory layout or footprints.
   - Proves that `asmTourRepWithPot` preserves `Local`, handle-in-footprint (`tourH ∈ foot`),
     `AsmBrOutProj` (P7), `AsmBrTourListProj` (readout 5), and `AsmBrBunAt` (P8/P5 restart),
     while supplying `bundleScanPotMul TS * tourPot R cord` directly inside `asmBrFullRep.phi`.
   - Proves `tourPot_le_mul_log`: at initialization, `tourPot R cord` is at most
     `2 * m * (Nat.log 2 (2 * m + 1) + 2)`, fitting inside `tr₀.machCost`.
2. **Bundle slot-block headroom invariant (`BundleCapHeadroom.lean`)**:
   re-exported from `MinCostFlow.SparseCore.Program.BundleCapHeadroom` (`bunNonEmpty`,
   `bunCapHeadroomInv`, `bunTableHeadroomInv`, and their preservation and `hcap_ok` lemmas).
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program
open MinCostFlow.SparseCore.Program.Restart

/-! ## 1. Uniqueness of core rotation lists and `asmTourRepWithPot` -/

private theorem tourBlocks_congr_order {G₁ G₂ F₀ : MGraph} (ρ₁ : Rotation G₁) (ρ₂ : Rotation G₂)
    (hord : ρ₁.order = ρ₂.order) :
    ∀ (n : ℕ) (F : MGraph) (hF : F.IsForest) (v : ℕ) (xs : List End),
      (compOf F v).card = n →
      tourBlocks G₁ F₀ ρ₁ F hF v xs = tourBlocks G₂ F₀ ρ₂ F hF v xs := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro F hF v xs hn
    rw [tourBlocks.eq_def G₁ F₀ ρ₁ F hF v xs, tourBlocks.eq_def G₂ F₀ ρ₂ F hF v xs]
    apply List.flatMap_congr
    intro x _
    by_cases h0 : x.1 ∈ F₀.E
    · simp only [h0, not_true_eq_false, ↓reduceIte]
      by_cases hg : x.1 ∈ F.E ∧ F.src x = v
      · rw [dite_eq_left hg, dite_eq_left hg, hord]
        have hlt : (compOf (eraseForestEdge F x.1) (F.dst x)).card < n := by
          rw [← hn, ← hg.2]
          exact branch_card_lt hF hg.1
        exact ih _ hlt _ _ _ _ rfl
      · rw [dite_eq_right hg, dite_eq_right hg]
    · simp [h0]

@[expose] public section

/-- Two core rotation list families that both match `(ord, rf)` under `TourCordOK` are equal. -/
theorem tourCordOK_unique {ord : ℕ → List End} {rf : RootedForest} {cord₁ cord₂ : ℕ → List End}
    (h₁ : TourCordOK ord rf cord₁) (h₂ : TourCordOK ord rf cord₂) : cord₁ = cord₂ := by
  obtain ⟨cs₁, ⟨_, _, hI₁, ρ₁, hρ₁, hc₁⟩, hf₁⟩ := h₁
  obtain ⟨cs₂, ⟨_, _, hI₂, ρ₂, hρ₂, hc₂⟩, hf₂⟩ := h₂
  have haux : ∀ {F₁ F₂ : MGraph} (h1 : F₁.IsForest) (h2 : F₂.IsForest) (v : ℕ),
      F₁ = F₂ → tour ρ₁ h1 v = tour ρ₂ h2 v := by
    intro F₁ F₂ h1 h2 v hFeq
    subst hFeq
    unfold tour
    have hord : ρ₁.order = ρ₂.order := hρ₁.trans hρ₂.symm
    have hblk := tourBlocks_congr_order (F₀ := F₁) ρ₁ ρ₂ hord (compOf F₁ v).card F₁ h1 v (ρ₁.order v) rfl
    simpa only [hord] using hblk
  funext v
  rw [hc₁, hc₂]
  simp only [coreRotation, hf₁, hf₂]
  split_ifs with hv
  · exact haux _ _ v rfl
  · rfl

/-- The tour potential `tourPot a.rf.R cord` of an abstract tour state `a : AsmTourAbs` (for the
unique core rotation `cord` matching `(a.ord, a.rf)` under `TourCordOK`, or `0` if none exists). -/
noncomputable def tourPotOfAbs (a : AsmTourAbs) : ℕ :=
  open Classical in
  if h : ∃ cord, TourCordOK a.ord a.rf cord then tourPot a.rf.R h.choose else 0

/-- Under `TourCordOK ord rf cord`, `tourPotOfAbs ⟨ord, rf, marks⟩ = tourPot rf.R cord`. -/
theorem tourPotOfAbs_eq_of_tourCordOK {ord : ℕ → List End} {rf : RootedForest}
    {cord : ℕ → List End} (marks : Finset End) (h : TourCordOK ord rf cord) :
    tourPotOfAbs ⟨ord, rf, marks⟩ = tourPot rf.R cord := by
  classical
  have hex : ∃ c, TourCordOK ord rf c := ⟨cord, h⟩
  simp only [tourPotOfAbs, hex, ↓reduceDIte]
  rw [tourCordOK_unique hex.choose_spec h]

/-- Wraps a tour representation family `TR` by adding `cPot eCap * tourPotOfAbs a` into its
potential, storing that ghost value in `τ` with identical memory representation and footprint. -/
noncomputable def asmTourRepWithPot (TR : ℕ → ℕ → DSRep AsmTourAbs) (cPot : ℕ → ℕ)
    (vCap eCap : ℕ) : DSRep AsmTourAbs where
  τ := (TR vCap eCap).τ × ℕ
  rep b a x mem := (TR vCap eCap).rep b a x.1 mem ∧ x.2 = cPot eCap * tourPotOfAbs a
  phi b x mem := (TR vCap eCap).phi b x.1 mem + x.2
  foot b x := (TR vCap eCap).foot b x.1

end

public section

theorem asmTourRepWithPot_local {TR : ℕ → ℕ → DSRep AsmTourAbs}
    (hTR : ∀ vCap eCap, (TR vCap eCap).Local) (cPot : ℕ → ℕ) (vCap eCap : ℕ) :
    (asmTourRepWithPot TR cPot vCap eCap).Local := by
  intro b a x mem mem' hag
  have h := hTR vCap eCap b a x.1 mem mem' hag
  exact ⟨fun ⟨hr, hp⟩ => ⟨h.1 hr, hp⟩, by dsimp [asmTourRepWithPot]; rw [h.2]⟩

theorem asmTourRepWithPot_foot_self {TR : ℕ → ℕ → DSRep AsmTourAbs}
    (hTh : ∀ vCap eCap tourH (tx : (TR vCap eCap).τ), (TR vCap eCap).foot tourH tx tourH)
    (cPot : ℕ → ℕ) (vCap eCap tourH : ℕ) (tx : (asmTourRepWithPot TR cPot vCap eCap).τ) :
    (asmTourRepWithPot TR cPot vCap eCap).foot tourH tx tourH :=
  hTh vCap eCap tourH tx.1

/-- `asmTourRepWithPot` preserves P7's tour projection `AsmBrOutProj`, because all four `OutTourAt`
operations leave `(ord, rf)` (and therefore `tourPotOfAbs`) unchanged. -/
theorem asmTourRepWithPot_outProj {OS : OutTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs} {w : ℕ}
    {p : Program} {nm sm fm lm : ℕ} (hOP : AsmBrOutProj OS TR w p nm sm fm lm) (cPot : ℕ → ℕ) :
    AsmBrOutProj OS (asmTourRepWithPot TR cPot) w p nm sm fm lm := by
  intro vCap eCap ord rf cord
  obtain ⟨⟨repT, hlocT, hnT, hsT, hfT, hlT⟩, hTrep⟩ := hOP vCap eCap ord rf cord
  subst hTrep
  have hloc : (asmTourView (asmTourRepWithPot TR cPot vCap eCap) ord rf cord).Local := by
    intro b s x mem mem' hag
    have h1 := hlocT b s x.1 mem mem' hag
    dsimp only [asmTourView] at h1
    exact ⟨fun ⟨hc, hok, hr, hp⟩ => ⟨hc, hok, (h1.1 ⟨hc, hok, hr⟩).2.2, hp⟩,
      by dsimp only [asmTourView, asmTourRepWithPot]; rw [h1.2]⟩
  refine ⟨⟨asmTourView (asmTourRepWithPot TR cPot vCap eCap) ord rf cord, hloc,
    ?_, ?_, ?_, ?_⟩, rfl⟩
  · intro tourH key v h s tx mem pos ω h1 h2 h3 h4 h5 h6 ⟨hc, hok, hr, hp⟩ hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, tx', hrun, hrep', hm', ho', hresp', hcost'⟩ :=
      hnT tourH key v h s tx.1 mem pos ω h1 h2 h3 h4 h5 h6 ⟨hc, hok, hr⟩ hfoot hz hsp
    refine ⟨body, hbody, o, st', c, (tx', tx.2), hrun, ⟨hrep'.1, hrep'.2.1, hrep'.2.2, hp⟩,
      hm', ho', hresp', ?_⟩
    dsimp [asmTourView, asmTourRepWithPot] at hcost' ⊢; omega
  · intro tourH key flag v h s tx mem pos ω h1 h2 h3 h4 h5 h6 h7 ⟨hc, hok, hr, hp⟩ hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, tx', hrun, hrep', hresp', hcost'⟩ :=
      hsT tourH key flag v h s tx.1 mem pos ω h1 h2 h3 h4 h5 h6 h7 ⟨hc, hok, hr⟩ hfoot hz hsp
    have hpotEq : tourPotOfAbs ⟨ord, rf, (s.setMark (endOfKey key) flag).marked⟩ =
        tourPotOfAbs ⟨ord, rf, s.marked⟩ := by
      rw [tourPotOfAbs_eq_of_tourCordOK _ hok, tourPotOfAbs_eq_of_tourCordOK _ hok]
    refine ⟨body, hbody, o, st', c, (tx', tx.2), hrun,
      ⟨hrep'.1, hrep'.2.1, hrep'.2.2, hp.trans (by rw [hpotEq])⟩, hresp', ?_⟩
    dsimp [asmTourView, asmTourRepWithPot] at hcost' ⊢; omega
  · intro tourH r h s tx mem pos ω h1 h2 h3 ⟨hc, hok, hr, hp⟩ hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, tx', hrun, hrep', hm', ho', hresp', hcost'⟩ :=
      hfT tourH r h s tx.1 mem pos ω h1 h2 h3 ⟨hc, hok, hr⟩ hfoot hz hsp
    refine ⟨body, hbody, o, st', c, (tx', tx.2), hrun, ⟨hrep'.1, hrep'.2.1, hrep'.2.2, hp⟩,
      hm', ho', hresp', ?_⟩
    dsimp [asmTourView, asmTourRepWithPot] at hcost' ⊢; omega
  · intro tourH r h s tx mem pos ω h1 h2 h3 ⟨hc, hok, hr, hp⟩ hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, tx', hrun, hrep', hm', ho', hresp', hcost'⟩ :=
      hlT tourH r h s tx.1 mem pos ω h1 h2 h3 ⟨hc, hok, hr⟩ hfoot hz hsp
    refine ⟨body, hbody, o, st', c, (tx', tx.2), hrun, ⟨hrep'.1, hrep'.2.1, hrep'.2.2, hp⟩,
      hm', ho', hresp', ?_⟩
    dsimp [asmTourView, asmTourRepWithPot] at hcost' ⊢; omega

/-- `asmTourRepWithPot` preserves readout 5's listing projection `AsmBrTourListProj`. -/
theorem asmTourRepWithPot_listProj {TR : ℕ → ℕ → DSRep AsmTourAbs} {w : ℕ} {p : Program}
    {f mul : ℕ} (hL : AsmBrTourListProj TR w p f mul) (cPot : ℕ → ℕ) :
    AsmBrTourListProj (asmTourRepWithPot TR cPot) w p f mul := by
  intro ord rf cord
  have h0 := hL ord rf cord
  refine ⟨fun vCap eCap tourH tx => h0.handle_foot vCap eCap tourH tx.1, ?_⟩
  intro vCap eCap tourH r h s tx mem pos ω h1 h2 h3 ⟨hc, hok, hr, hp⟩ hfoot hz hsp
  obtain ⟨body, hbody, o, st', c, tx', hrun, hrep', hEL, ho', hz', hfr', hft', hcost'⟩ :=
    h0.runs vCap eCap tourH r h s tx.1 mem pos ω h1 h2 h3 ⟨hc, hok, hr⟩ hfoot hz hsp
  refine ⟨body, hbody, o, st', c, (tx', tx.2), hrun, ⟨hrep'.1, hrep'.2.1, hrep'.2.2, hp⟩,
    hEL, ho', hz', hfr', hft', ?_⟩
  dsimp [asmTourView, asmTourRepWithPot] at hcost' ⊢; omega

/-- `asmTourRepWithPot` preserves P5's bundle-tour projection `AsmBrTourBridge`, because all three
`BundleTourAt` operations (`list`, `len`, `owner`) are read-only on `(ord, rf, marks)`. -/
theorem asmTourRepWithPot_bundleBridge {TS : BundleTourSpec} {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {w : ℕ} {p : Program} {idxList idxLen idxOwner : ℕ}
    (hB : AsmBrTourBridge TS TR w p idxList idxLen idxOwner) (cPot : ℕ → ℕ) :
    AsmBrTourBridge TS (asmTourRepWithPot TR cPot) w p idxList idxLen idxOwner := by
  intro vCap eCap vo vf vc mk
  obtain ⟨⟨repT, hlocT, hlistT, hlenT, hownT⟩, hTrep⟩ := hB vCap eCap vo vf vc mk
  subst hTrep
  have hloc : (asmTourCordView (asmTourRepWithPot TR cPot vCap eCap) vo vf vc mk).Local := by
    intro b s x mem mem' hag
    have h1 := hlocT b s x.1 mem mem' hag
    dsimp only [asmTourCordView, cordRepM, asmTourView] at h1
    exact ⟨fun ⟨hc, hok, hr, hp⟩ => ⟨hc, hok, (h1.1 ⟨hc, hok, hr⟩).2.2, hp⟩,
      by dsimp only [asmTourCordView, cordRepM, asmTourView, asmTourRepWithPot]; rw [h1.2]⟩
  refine ⟨⟨asmTourCordView (asmTourRepWithPot TR cPot vCap eCap) vo vf vc mk, hloc,
    ?_, ?_, ?_⟩, rfl⟩
  · intro tourH v h cord tx mem pos ω h1 h2 h3 h4 ⟨hc, hok, hr, hp⟩ hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, tx', hrun, hrep', hEL, ho', hresp', hcost'⟩ :=
      hlistT tourH v h cord tx.1 mem pos ω h1 h2 h3 h4 ⟨hc, hok, hr⟩ hfoot hz hsp
    refine ⟨body, hbody, o, st', c, (tx', tx.2), hrun, ⟨hrep'.1, hrep'.2.1, hrep'.2.2, hp⟩,
      hEL, ho', hresp', ?_⟩
    dsimp [asmTourCordView, cordRepM, asmTourView, asmTourRepWithPot] at hcost' ⊢; omega
  · intro tourH v h cord tx mem pos ω h1 h2 h3 h4 ⟨hc, hok, hr, hp⟩ hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, tx', hrun, hrep', hm', ho', hresp', hcost'⟩ :=
      hlenT tourH v h cord tx.1 mem pos ω h1 h2 h3 h4 ⟨hc, hok, hr⟩ hfoot hz hsp
    refine ⟨body, hbody, o, st', c, (tx', tx.2), hrun, ⟨hrep'.1, hrep'.2.1, hrep'.2.2, hp⟩,
      hm', ho', hresp', ?_⟩
    dsimp [asmTourCordView, cordRepM, asmTourView, asmTourRepWithPot] at hcost' ⊢; omega
  · intro tourH key v h cord tx mem pos ω h1 h2 h3 h4 h5 h6 h7 ⟨hc, hok, hr, hp⟩ hfoot hz hsp
    obtain ⟨body, hbody, o, st', c, tx', hrun, hrep', hm', ho', hresp', hcost'⟩ :=
      hownT tourH key v h cord tx.1 mem pos ω h1 h2 h3 h4 h5 h6 h7 ⟨hc, hok, hr⟩ hfoot hz hsp
    refine ⟨body, hbody, o, st', c, (tx', tx.2), hrun, ⟨hrep'.1, hrep'.2.1, hrep'.2.2, hp⟩,
      hm', ho', hresp', ?_⟩
    dsimp [asmTourCordView, cordRepM, asmTourView, asmTourRepWithPot] at hcost' ⊢; omega

/-- `asmTourRepWithPot` preserves P5's restart interface `AsmBrBunAt`, since a restart keeps
`(ord, rf, cord)` unchanged. -/
def asmTourRepWithPot_bunAt {TR : ℕ → ℕ → DSRep AsmTourAbs}
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)} {w : ℕ}
    {p : Program} {f : ℕ} (J : AsmBrBunAt TR B5 w p f) (cPot : ℕ → ℕ) :
    AsmBrBunAt (asmTourRepWithPot TR cPot) B5 w p f where
  mul := J.mul
  space := J.space
  space_le := J.space_le
  rep_local := J.rep_local
  runs := by
    intro k slotCap vCap₅ eCap₅ vCap eCap vo vf vc mk hv he h2e hvW
      tbl tourH slotsPtr h slots S x cord tx cs ord mem pos ω
      h1 h2 h3 h4 h5 hLA hSL hnd hE hk hcore hinv hB ⟨hc, hok, hr, hp⟩ hfb hft hdisj hz hsp
    obtain ⟨body, hbody, o, st', c, S', x', tx', hrun, hB', hT', hinv', hoth, hslot,
      hlo, hhi, hz', hfr, hgb, hgt, hd', hcost⟩ :=
      J.runs k slotCap vCap₅ eCap₅ vCap eCap vo vf vc mk hv he h2e hvW
        tbl tourH slotsPtr h slots S x cord tx.1 cs ord mem pos ω
        h1 h2 h3 h4 h5 hLA hSL hnd hE hk hcore hinv hB ⟨hc, hok, hr⟩ hfb hft hdisj hz hsp
    refine ⟨body, hbody, o, st', c, S', x', (tx', tx.2), hrun, hB',
      ⟨hT'.1, hT'.2.1, hT'.2.2, hp⟩, hinv', hoth, hslot, hlo, hhi, hz', hfr, hgb, hgt, hd', ?_⟩
    dsimp [asmTourCordView, cordRepM, asmTourView, asmTourRepWithPot] at hcost ⊢; omega

/-- Initial upper bound on `tourPot`: whenever `∑ r ∈ R, (cord r).length ≤ 2 * m`,
`tourPot R cord ≤ (Nat.log 2 (2 * m + 1) + 2) * (2 * m)`. -/
theorem tourPot_le_mul_log {R : Finset ℕ} {cord : ℕ → List End} {m : ℕ}
    (hsum : (∑ r ∈ R, (cord r).length) ≤ 2 * m) :
    tourPot R cord ≤ (Nat.log 2 (2 * m + 1) + 2) * (2 * m) := by
  unfold tourPot
  calc ∑ r ∈ R, tourPotTerm (cord r).length
      ≤ ∑ r ∈ R, (Nat.log 2 (2 * m + 1) + 2) * (cord r).length := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hle : (cord r).length ≤ 2 * m :=
          (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hr).trans hsum
        unfold tourPotTerm
        split_ifs with hz
        · exact Nat.zero_le _
        · have hlog : Nat.log 2 (cord r).length ≤ Nat.log 2 (2 * m + 1) :=
            Nat.log_mono_right (by omega)
          exact (Nat.sub_le _ _).trans (Nat.mul_le_mul_right _ (by omega))
    _ = (Nat.log 2 (2 * m + 1) + 2) * ∑ r ∈ R, (cord r).length := by
        rw [← Finset.mul_sum]
    _ ≤ (Nat.log 2 (2 * m + 1) + 2) * (2 * m) := Nat.mul_le_mul_left _ hsum

end

end MinCostFlow.SparseCore.Program
