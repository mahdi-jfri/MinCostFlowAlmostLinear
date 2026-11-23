module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActLoop
public import MinCostFlow.SparseCore.Program.AssemblyFirstNewPairs
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitBoundCost
public import MinCostFlow.SparseCore.Program.AssemblyFirstInitMidFacts

import Mathlib.Tactic

/-!
# Phase 2b pure math, space/cost bounds, and `specPhi` delta (`AssemblyFirstStepNewActMath`)

Provides the space and cost definitions (`newActTotalSpace`, `newActCostMul`), `spanAfter` lookup
and `specPhi` delta lemmas (`spanAfter_of_not_mem`, `spanAfter_of_mem`, `specPhi_spanAfter_disj`),
and the full Phase 2b amortized cost bound (`asmFirstNewAct_cost_bound`) linking `rangeCost` of
`newActLoopStepCost` and P6's spanner-activation costs/banks to `newSet.sum tr.lazyMachInitCost`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program.Restart

/-! ## 1. Space and cost definitions -/

@[expose] public section

/-- Total heap space allocated by `asmFirstNewActStmt`: `lazyTbl` (`2 * |newComps|`), the
component-init loop (`newActLoopSpace`), and P6's spanner activations (`asmFiSpanCapSpace`). -/
noncomputable def newActTotalSpace {depth : ℕ} (TS : BundleTourSpec) (rQ : ℕ)
    (impl : SparsifyImpl) (w : ℕ)
    (y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth)
    (tr : BundleTreeState depth) (ord : ℕ → List End) (newComps : List (ℕ × ℕ)) : ℕ :=
  let P := asmBrSP impl w depth y
  2 * newComps.length + newActLoopSpace TS rQ tr ord y.comps newComps +
    newCompsBucketSum tr y.comps newComps *
      (10 + 13 * P.eCap + P.vCap + asmFiSpanCapSpace P) + 200

/-- Cost multiplier for `asmFirstNewActStmt` (against `ordStoreLog y.eCap5`). -/
def newActCostMul (TS : BundleTourSpec) (rMul : ℕ) : ℕ :=
  rMul + 4 * TS.mul + 4500

end

/-! ## 2. Pure helpers -/

public section

lemma inactive_cord_len_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {depth : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    (hCross : AsmFirstCrossInactiveInv tr)
    {C : Finset ℕ} (hC : C ∈ components tr.cs.G₀) (hNotAct : C ∉ tr.activeComps)
    (hR1 : (tr.cs.compSt C).R.card = 1) {v : ℕ} (hv : v ∈ (tr.cs.compSt C).G.V) :
    (outCoreOrder tr ord (tr.cs.RF.root v)).length = 2 * (compCoreEdges tr C).card := by
  classical
  obtain ⟨hIff, -, -⟩ := inactive_comp_cord_iff hI ρ hρ hC hNotAct hR1 hCross hv
  have hnd : (outCoreOrder tr ord (tr.cs.RF.root v)).Nodup := by
    have hex : ∃ (C' : ℝ) (ℓ : ℕ → ℝ) (_ : CompLSFInv C' ℓ tr.cs) (ρ' : Rotation tr.cs.G),
        ρ'.order = ord := ⟨C_lsst, ℓ₀, hI, ρ, hρ⟩
    unfold outCoreOrder; rw [dite_eq_left hex]
    exact (coreRotation (L := tr.cs.lsf) hex.choose_spec.choose_spec.choose_spec.choose
      hex.choose_spec.choose_spec.choose.hG_val (compLSF_RF_isRSF hex.choose_spec.choose_spec.choose)).nodup _
  rw [← List.toFinset_card_of_nodup hnd]
  have hset : (outCoreOrder tr ord (tr.cs.RF.root v)).toFinset =
      compCoreEdges tr C ×ˢ ({false, true} : Finset Bool) := by
    ext ⟨e, side⟩
    simp only [List.mem_toFinset, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton,
      compCoreEdges, Finset.mem_filter]
    rw [hIff (e, side)]
    cases side <;> simp
  rw [hset, Finset.card_product]
  have h2 : ({false, true} : Finset Bool).card = 2 := by decide
  rw [h2]; omega

lemma inactive_compCoreEdges_card_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {depth : ℕ}
    {tr : BundleTreeState depth} {ord : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    {C : Finset ℕ}
    (hBktsEq : tr.activeBuckets C = (compCoreEdges tr C).image tr.origBucket)
    (hLazyBun : ∀ b ∈ tr.activeBuckets C,
      BunAgree (initBundleFor tr.cs ord
        (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b) tr.k)
        (tr.bun (C, b)) ∧
      tr.initBunG (C, b) = normGraph (tr.bun (C, b)).graph) :
    (compCoreEdges tr C).card = (tr.activeBuckets C).sum fun b => (tr.initBunG (C, b)).m := by
  classical
  have hpart : compCoreEdges tr C =
      (tr.activeBuckets C).biUnion fun b =>
        bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b := by
    ext e
    simp only [compCoreEdges, bucketCoreEdges, Finset.mem_biUnion, Finset.mem_filter, hBktsEq,
      Finset.mem_image]
    constructor
    · intro ⟨he, ht⟩
      exact ⟨tr.origBucket e, ⟨e, ⟨he, ht⟩, rfl⟩, he, ht, rfl⟩
    · rintro ⟨_, _, he, ht, _⟩
      exact ⟨he, ht⟩
  rw [hpart, Finset.card_biUnion]
  · refine Finset.sum_congr rfl fun b hb => ?_
    obtain ⟨hag, hinit⟩ := hLazyBun b hb
    have hE1 : (initBundleFor tr.cs ord
        (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b) tr.k).edges =
        bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b :=
      initBundleFor_edges hI hρ _ tr.k
    have hE2 : (tr.initBunG (C, b)).E = (tr.bun (C, b)).edges := by
      rw [hinit, normGraph_E]; rfl
    show (bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b).card =
      (tr.initBunG (C, b)).E.card
    rw [hE2, ← hag.2.1, hE1]
  · intro b₁ _ b₂ _ hne
    refine Finset.disjoint_left.mpr fun e h1 h2 => ?_
    simp only [bucketCoreEdges, Finset.mem_filter] at h1 h2
    exact hne (h1.2.2.symm.trans h2.2.2)

lemma newActLoopStepCost_le {TS : BundleTourSpec} {rMul eCap depth : ℕ}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {tr : BundleTreeState depth} {ord : ℕ → List End}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    (hCross : AsmFirstCrossInactiveInv tr) (heCapG : ∀ e ∈ tr.cs.G.E, e < eCap)
    {comps : List (Finset ℕ)} {c v : ℕ} (hc : c < comps.length)
    (hC : comps[c] ∈ components tr.cs.G₀) (hNotAct : comps[c] ∉ tr.activeComps)
    (hR1 : (tr.cs.compSt comps[c]).R.card = 1)
    (hBktsEq : tr.activeBuckets comps[c] = (compCoreEdges tr comps[c]).image tr.origBucket)
    (hv : v ∈ (tr.cs.compSt comps[c]).G.V) :
    newActLoopStepCost TS rMul eCap tr ord comps (c, v) ≤
      (rMul + 4 * TS.mul + 3500) * ((compCoreEdges tr comps[c]).card + 1) * ordStoreLog eCap := by
  set C := comps[c]'hc
  set mC := (compCoreEdges tr C).card
  set r := (tr.activeBuckets C).card
  set lg := ordStoreLog eCap
  have hlg1 : 1 ≤ lg := by unfold lg ordStoreLog; omega
  have hlen : (outCoreOrder tr ord (tr.cs.RF.root v)).length = 2 * mC :=
    inactive_cord_len_eq hI ρ hρ hCross hC hNotAct hR1 hv
  have hr_le : r ≤ mC := by
    rw [show r = ((compCoreEdges tr C).image tr.origBucket).card from by rw [← hBktsEq]]
    exact Finset.card_image_le
  have hmC_le : mC ≤ eCap := by
    have hsub : compCoreEdges tr C ⊆ Finset.range eCap := fun e he => by
      have heG : e ∈ tr.cs.G.E := (Finset.mem_sdiff.mp (Finset.mem_filter.mp he).1).1
      exact Finset.mem_range.mpr (heCapG e heG)
    exact (Finset.card_le_card hsub).trans (by simp)
  have hlog_2m : Nat.log 2 (2 * mC + 1) + 1 ≤ 2 * lg := by
    have h1 : 2 * mC + 1 ≤ 2 * (eCap + 2) := by omega
    have h2 : Nat.log 2 (2 * mC + 1) ≤ Nat.log 2 (2 * (eCap + 2)) := Nat.log_mono_right h1
    have h3 : Nat.log 2 (2 * (eCap + 2)) = Nat.log 2 (eCap + 2) + 1 := by
      rw [Nat.mul_comm, Nat.log_mul_base (by decide) (by omega)]
    unfold lg ordStoreLog at *; omega
  have hlog_m : Nat.log 2 (mC + 1) + 1 ≤ lg := by
    have h1 : Nat.log 2 (mC + 1) ≤ Nat.log 2 (eCap + 2) := Nat.log_mono_right (by omega)
    unfold lg ordStoreLog at *; omega
  have hlog_r : Nat.log 2 (r + 1) + 1 ≤ lg := by
    have h1 : Nat.log 2 (r + 1) ≤ Nat.log 2 (eCap + 2) := Nat.log_mono_right (by omega)
    unfold lg ordStoreLog at *; omega
  have hprep : newActPrepCost (2 * mC) mC r ≤ 1700 * mC * lg + 500 := by
    unfold newActPrepCost
    have t1 : 200 * (2 * mC) * (Nat.log 2 (2 * mC + 1) + 1) ≤ 800 * mC * lg := by
      have := Nat.mul_le_mul_left (400 * mC) hlog_2m; nlinarith
    have t2 : 200 * mC * (Nat.log 2 (mC + 1) + 1) ≤ 200 * mC * lg := by
      have := Nat.mul_le_mul_left (200 * mC) hlog_m; nlinarith
    have t3 : mC * (45 * (Nat.log 2 (r + 1) + 1) + 80) ≤ 125 * mC * lg := by
      have : 45 * (Nat.log 2 (r + 1) + 1) + 80 ≤ 125 * lg := by nlinarith
      exact (Nat.mul_le_mul_left mC this).trans (by nlinarith)
    have t4 : 120 * (2 * mC) + 120 * mC + 120 * r ≤ 480 * mC * lg := by nlinarith
    linarith
  have hinit : bundleInitSlotsCost TS eCap r mC (outCoreOrder tr ord) [tr.cs.RF.root v] ≤
      (2 * TS.mul + 700) * mC * lg + (TS.mul + 450) * lg := by
    unfold bundleInitSlotsCost
    simp only [List.length_singleton, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Nat.add_zero, hlen]
    nlinarith
  have helse : newActElseCost TS eCap (2 * mC) mC r (outCoreOrder tr ord) (tr.cs.RF.root v) ≤
      (2 * TS.mul + 3000) * mC * lg + (TS.mul + 1000) * lg := by
    unfold newActElseCost bunPhiMul
    have h600 : 300 * (2 * mC) ≤ 600 * mC * lg := by nlinarith
    nlinarith
  unfold newActLoopStepCost newActOneCost
  rw [List.getD_eq_getElem comps ∅ hc]
  change rMul * lg + TS.mul * ((outCoreOrder tr ord (tr.cs.RF.root v)).length + 1) * lg +
      (if (outCoreOrder tr ord (tr.cs.RF.root v)).length = 0 then 0
       else newActElseCost TS eCap (outCoreOrder tr ord (tr.cs.RF.root v)).length mC r
         (outCoreOrder tr ord) (tr.cs.RF.root v)) + 100 + 40 ≤
      (rMul + 4 * TS.mul + 3500) * (mC + 1) * lg
  rw [hlen]
  have h140 : 140 ≤ 140 * lg := by nlinarith
  have hE1 : (2 * TS.mul + 3000) * mC * lg = 2 * (TS.mul * mC * lg) + 3000 * (mC * lg) := by ring
  have hE2 : (TS.mul + 1000) * lg = TS.mul * lg + 1000 * lg := by ring
  have hTS : TS.mul * (2 * mC + 1) * lg = 2 * (TS.mul * mC * lg) + TS.mul * lg := by ring
  have hR : (rMul + 4 * TS.mul + 3500) * (mC + 1) * lg =
      rMul * mC * lg + rMul * lg + 4 * (TS.mul * mC * lg) + 4 * (TS.mul * lg) + 3500 * (mC * lg) + 3500 * lg := by ring
  rw [hTS, hR]; rw [hE1, hE2] at helse
  split_ifs <;> omega

lemma spanAfter_of_not_mem {cap : ℕ} (S : BucketSpannerState cap) (g : ℕ → MGraph)
    {l : List ℕ} {j : Fin cap} (hnot : j.1 ∉ l) : spanAfter S g l j = S j := by
  simp [spanAfter, hnot]

lemma spanAfter_of_mem {cap : ℕ} (S : BucketSpannerState cap) (g : ℕ → MGraph)
    {l : List ℕ} {j : Fin cap} (hmem : j.1 ∈ l) : spanAfter S g l j = some ⟨g j.1, []⟩ := by
  simp [spanAfter, hmem]

lemma specPhi_spanAfter_disj {P : DSParams} {cap : ℕ}
    (S6 : BucketSpannerState cap) (g : ℕ → MGraph) :
    ∀ (slots : List ℕ), slots.Nodup → (∀ s ∈ slots, s < cap) →
      (∀ s ∈ slots, ∀ hs : s < cap, S6 ⟨s, hs⟩ = none) →
      specPhi P (spanAfter S6 g slots) = specPhi P S6 + (slots.map fun s => dsInitBank P (g s)).sum
  | [], _, _, _ => by simp [specPhi, spanAfter]
  | s :: rest, hnd, hlt, hnone => by
    obtain ⟨hs_not, hnd_rest⟩ := List.nodup_cons.mp hnd
    have hs_lt : s < cap := hlt s List.mem_cons_self
    set S1 : BucketSpannerState cap := S6.set ⟨s, hs_lt⟩ (some ⟨g s, []⟩)
    have hstep : spanAfter S6 g (s :: rest) = spanAfter S1 g rest := by
      funext j
      by_cases hr : j.1 ∈ rest
      · simp [spanAfter, hr]
      · by_cases hj : j.1 = s
        · have hjEq : j = ⟨s, hs_lt⟩ := Fin.ext hj
          subst hjEq; simp [spanAfter, S1, BucketSpannerState.set, hr]
        · have hne : j ≠ ⟨s, hs_lt⟩ := fun h => hj (congrArg Fin.val h)
          simp [spanAfter, S1, BucketSpannerState.set, Function.update_of_ne hne, hr, hj]
    have hnone_rest : ∀ t ∈ rest, ∀ ht : t < cap, S1 ⟨t, ht⟩ = none := fun t ht hlt_t => by
      have hne : (⟨t, hlt_t⟩ : Fin cap) ≠ ⟨s, hs_lt⟩ := fun h => by
        have hts : t = s := congrArg Fin.val h
        exact hs_not (hts ▸ ht)
      simp only [S1, BucketSpannerState.set, Function.update_of_ne hne]
      exact hnone t (List.mem_cons_of_mem s ht) hlt_t
    have ih := specPhi_spanAfter_disj (P := P) S1 g rest hnd_rest
      (fun t ht => hlt t (List.mem_cons_of_mem s ht)) hnone_rest
    rw [hstep, ih]
    have hS1_phi : specPhi P S1 = specPhi P S6 + dsInitBank P (g s) := by
      unfold specPhi
      have hsub : ∀ j : Fin cap, j ≠ ⟨s, hs_lt⟩ →
          (match S1 j with | some d => d.bank P | none => 0) =
          (match S6 j with | some d => d.bank P | none => 0) := fun j hj => by
        simp [S1, BucketSpannerState.set, Function.update_of_ne hj]
      have ha1 := Finset.add_sum_erase Finset.univ (fun j => match S1 j with | some d => d.bank P | none => 0) (Finset.mem_univ ⟨s, hs_lt⟩)
      have ha6 := Finset.add_sum_erase Finset.univ (fun j => match S6 j with | some d => d.bank P | none => 0) (Finset.mem_univ ⟨s, hs_lt⟩)
      have hrest_eq : ∑ j ∈ Finset.univ.erase ⟨s, hs_lt⟩, (match S1 j with | some d => d.bank P | none => 0) =
          ∑ j ∈ Finset.univ.erase ⟨s, hs_lt⟩, (match S6 j with | some d => d.bank P | none => 0) :=
        Finset.sum_congr rfl fun j hj => hsub j (Finset.ne_of_mem_erase hj)
      have h0 : S6 ⟨s, hs_lt⟩ = none := hnone s List.mem_cons_self hs_lt
      have h1 : S1 ⟨s, hs_lt⟩ = some ⟨g s, []⟩ := by simp [S1, BucketSpannerState.set]
      rw [h1] at ha1; rw [h0] at ha6
      dsimp only at ha1 ha6
      rw [dsHist_nil_bank_eq_dsInitBank] at ha1
      change (∑ j ∈ Finset.univ, match S1 j with | some d => d.bank P | none => 0) =
          (∑ j ∈ Finset.univ, match S6 j with | some d => d.bank P | none => 0) + dsInitBank P (g s)
      rw [← ha1, ← ha6, hrest_eq]; omega
    rw [hS1_phi]; simp only [List.map_cons, List.sum_cons]; omega

lemma rangeCost_eq_sum_map {α : Type*} (f : α → ℕ) (d : α) (L : List α) :
    rangeCost (fun i => f (L.getD i d)) 0 L.length = (L.map f).sum := by
  have haux : ∀ k i, k = L.length - i → i ≤ L.length →
      rangeCost (fun j => f (L.getD j d)) i L.length = ((L.drop i).map f).sum := by
    intro k
    induction k with
    | zero =>
      intro i hk hi
      have heq : i = L.length := by omega
      subst heq; rw [rangeCost_of_le (le_refl _)]; simp
    | succ k ih =>
      intro i hk hi
      have hlt : i < L.length := by omega
      rw [rangeCost_step hlt, ih (i + 1) (by omega) (by omega)]
      rw [List.drop_eq_getElem_cons hlt, List.map_cons, List.sum_cons, List.getD_eq_getElem L d hlt]
  simpa using haux L.length 0 (by omega) (Nat.zero_le _)

private lemma list_map_sum_le_of_mem {α : Type*} {f g : α → ℕ} :
    ∀ (L : List α), (∀ x ∈ L, f x ≤ g x) → (L.map f).sum ≤ (L.map g).sum
  | [], _ => Nat.le_refl 0
  | x :: xs, h => by
    simp only [List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h x List.mem_cons_self)
      (list_map_sum_le_of_mem xs fun y hy => h y (List.mem_cons_of_mem x hy))

/-! ## 3. Phase 2b combined amortized cost bound -/

/-- Combines the component-init loop cost bound and the spanner-activation cost/bank bound into a
single bound against `newSet.sum tr.lazyMachInitCost`. The spanner potential is counted `K` times
(the side potential uses `K = 320 * (capExp + 1) * y.lgFac`); the new banks then cost
`K * newSet.sum tr.lazyMachInitCost`. -/
lemma asmFirstNewAct_cost_bound {TS : BundleTourSpec} {rMul w depth K : ℕ} {impl : SparsifyImpl}
    {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {tr : BundleTreeState depth} {ord : ℕ → List End}
    {y : AsmBrSide (fun kB slotCap vCap eCap => bunTableHeadroomRep slotCap vCap eCap kB) depth}
    {newComps : List (ℕ × ℕ)} {S1 : BundleTableState y.slotCap} {slotOf1 : Finset ℕ × ℤ → ℕ}
    {cLoop cSpan phiB0 phiB1 phiT0 phiT1 : ℕ}
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (ρ : Rotation tr.cs.G) (hρ : ρ.order = ord)
    (hCross : AsmFirstCrossInactiveInv tr) (heCapG : ∀ e ∈ tr.cs.G.E, e < y.eCap5)
    (hCompsNd : y.comps.Nodup) (hCompsMem : ∀ C, C ∈ y.comps ↔ C ∈ components tr.cs.G₀)
    (hSlotMap0 : SlotMapOK tr y.slotCap y.cap y.slots y.slotOf)
    (hSlotsRange : y.slots = List.range y.slots.length)
    (hFreeSpan0 : ∀ j : Fin y.cap, j.1 ∉ y.slots → y.spanS j = none)
    (hParamsLe : SparsifyParamsLe (canonicalSparsifyParams impl y.mMax).absorbTime tr.spanParams)
    (hSpanC : dsAmortConst impl ≤ tr.spanConst) (hSplitEq : y.splitB = tr.splitBound)
    (hLazyBound : ∀ C ∉ tr.activeComps, ((tr.activeBuckets C).sum fun b => tr.spanConst *
      spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))) ≤ tr.lazyMachInitCost C)
    (hInactiveInv : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hNC_nd : (newComps.map Prod.fst).Nodup)
    (hNC_ok : ∀ q ∈ newComps, ∃ hc : q.1 < y.comps.length,
      y.comps[q.1]'hc ∉ tr.activeComps ∧ q.2 ∈ (tr.cs.compSt (y.comps[q.1]'hc)).G.V)
    (hSlotMap1 : SlotMapOK { tr with activeComps := tr.activeComps ∪
        (newComps.map fun p => y.comps.getD p.1 ∅).toFinset }
      y.slotCap y.cap (List.range (y.slots.length + newCompsBucketSum tr y.comps newComps)) slotOf1)
    (hBunMatch1 : BunTableMatches { tr with activeComps := tr.activeComps ∪
        (newComps.map fun p => y.comps.getD p.1 ∅).toFinset } slotOf1 S1)
    (hOldSlot1 : ∀ q ∈ activePairs tr, slotOf1 q = y.slotOf q)
    (hLoopC : cLoop + phiB1 + phiT1 ≤
      rangeCost (fun i => newActLoopStepCost TS rMul y.eCap5 tr ord y.comps (newComps.getD i (0, 0))) 0 newComps.length +
        newComps.length * 9 + 7 + phiB0 + phiT0)
    (hSpanC_le : let P := asmBrSP impl w depth y
      let newSlots := List.range' y.slots.length (newCompsBucketSum tr y.comps newComps)
      cSpan + specPhi P (spanAfter y.spanS (asmFirstInitSlotGraph S1) newSlots) ≤
        specPhi P y.spanS +
        (newSlots.map fun s => bundleExportCost (slotB S1 s)).sum +
        (newSlots.map fun s => spanActivateCost P (asmFirstInitSlotGraph S1 s)).sum +
        200 * newSlots.length + 300) :
    let newSet : Finset (Finset ℕ) := (newComps.map fun p => y.comps.getD p.1 ∅).toFinset
    let P := asmBrSP impl w depth y
    let S6' := spanAfter y.spanS (asmFirstInitSlotGraph S1) (List.range' y.slots.length (newCompsBucketSum tr y.comps newComps))
    cLoop + cSpan + phiB1 + K * specPhi P S6' + phiT1 + 50 ≤
      newActCostMul TS rMul * (newComps.length + 1 + newSet.sum tr.lazyMachInitCost) * ordStoreLog y.eCap5 +
      K * newSet.sum tr.lazyMachInitCost + phiB0 + K * specPhi P y.spanS + phiT0 := by
  intro newSet P S6'
  set tr_mid : BundleTreeState depth := { tr with activeComps := tr.activeComps ∪ newSet }
  set nSlots1 := y.slots.length + newCompsBucketSum tr y.comps newComps
  set newSlots := List.range' y.slots.length (newCompsBucketSum tr y.comps newComps)
  have hlg1 : 1 ≤ ordStoreLog y.eCap5 := by unfold ordStoreLog; omega
  have hnewSlots_nd : newSlots.Nodup := List.nodup_range'
  have hnewSlots_mem : ∀ s, s ∈ newSlots ↔ y.slots.length ≤ s ∧ s < nSlots1 := fun s => by
    simp [newSlots, List.mem_range'_1, nSlots1]
  have hnew_list_nd : (newComps.map fun p => y.comps.getD p.1 ∅).Nodup := by
    rw [List.nodup_iff_injective_getElem]
    intro i j hij
    have hi : i.1 < newComps.length := by simpa using i.2
    have hj : j.1 < newComps.length := by simpa using j.2
    have hci := (hNC_ok _ (List.getElem_mem hi)).1
    have hcj := (hNC_ok _ (List.getElem_mem hj)).1
    simp only [List.getElem_map, List.getD_eq_getElem _ _ hci, List.getD_eq_getElem _ _ hcj] at hij
    have hEq_c : newComps[i.1].1 = newComps[j.1].1 := congrArg Fin.val
      ((List.nodup_iff_injective_getElem.mp hCompsNd) (a₁ := ⟨newComps[i.1].1, hci⟩) (a₂ := ⟨newComps[j.1].1, hcj⟩) hij)
    have hEq_i := (List.nodup_iff_injective_getElem.mp hNC_nd) (a₁ := ⟨i.1, by simpa using hi⟩) (a₂ := ⟨j.1, by simpa using hj⟩) (by simpa using hEq_c)
    exact Fin.ext (by simpa using congrArg Fin.val hEq_i)
  have hLoopRange_le : rangeCost (fun i => newActLoopStepCost TS rMul y.eCap5 tr ord y.comps (newComps.getD i (0, 0))) 0 newComps.length ≤
      (rMul + 4 * TS.mul + 3500) * (newSet.sum tr.lazyMachInitCost + newComps.length) * ordStoreLog y.eCap5 := by
    rw [rangeCost_eq_sum_map]
    have h1 : (newComps.map fun p => newActLoopStepCost TS rMul y.eCap5 tr ord y.comps p).sum ≤
        (newComps.map fun p => (rMul + 4 * TS.mul + 3500) * (tr.lazyMachInitCost (y.comps.getD p.1 ∅) + 1) * ordStoreLog y.eCap5).sum := by
      refine list_map_sum_le_of_mem newComps fun p hp => ?_
      obtain ⟨hc_i, hNotAct_i, hv_i⟩ := hNC_ok p hp
      have hC_mem : y.comps[p.1]'hc_i ∈ components tr.cs.G₀ := (hCompsMem _).mp (List.getElem_mem hc_i)
      obtain ⟨hR1_i, hBkts_i, _, _, hLz_i⟩ := hInactiveInv _ hC_mem hNotAct_i
      have hstep := newActLoopStepCost_le (TS := TS) (rMul := rMul) (eCap := y.eCap5) hI ρ hρ hCross heCapG
        hc_i hC_mem hNotAct_i hR1_i hBkts_i hv_i
      have hmC_le_lz : (compCoreEdges tr (y.comps[p.1]'hc_i)).card ≤ tr.lazyMachInitCost (y.comps[p.1]'hc_i) := by
        rw [inactive_compCoreEdges_card_eq hI ρ hρ hBkts_i (fun b hb => ⟨(hLz_i b hb).1, (hLz_i b hb).2.1⟩)]
        refine (Finset.sum_le_sum fun b hb => ?_).trans (hLazyBound _ hNotAct_i)
        have h1' := n_add_m_add_one_le_spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (y.comps[p.1]'hc_i, b))
        have h2' := Nat.le_mul_of_pos_left (spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (y.comps[p.1]'hc_i, b)))
          ((one_le_dsAmortConst impl).trans hSpanC)
        omega
      rw [List.getD_eq_getElem y.comps ∅ hc_i]
      exact hstep.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.add_le_add_right hmC_le_lz 1)))
    have h2 : (newComps.map fun p => (rMul + 4 * TS.mul + 3500) * (tr.lazyMachInitCost (y.comps.getD p.1 ∅) + 1) * ordStoreLog y.eCap5).sum =
        (rMul + 4 * TS.mul + 3500) * (newSet.sum tr.lazyMachInitCost + newComps.length) * ordStoreLog y.eCap5 := by
      have hfact : ∀ L : List (ℕ × ℕ),
          (L.map fun p => (rMul + 4 * TS.mul + 3500) * (tr.lazyMachInitCost (y.comps.getD p.1 ∅) + 1) * ordStoreLog y.eCap5).sum =
          (rMul + 4 * TS.mul + 3500) * ((L.map fun p => tr.lazyMachInitCost (y.comps.getD p.1 ∅)).sum + L.length) * ordStoreLog y.eCap5 := by
        intro L; induction L with
        | nil => simp
        | cons a t ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring
      rw [hfact]
      have hsum_eq : (newComps.map fun p => tr.lazyMachInitCost (y.comps.getD p.1 ∅)).sum = newSet.sum tr.lazyMachInitCost := by
        have : (newComps.map fun p => tr.lazyMachInitCost (y.comps.getD p.1 ∅)) =
            (newComps.map fun p => y.comps.getD p.1 ∅).map tr.lazyMachInitCost := by simp [List.map_map, Function.comp_def]
        rw [this, ← List.sum_toFinset _ hnew_list_nd]
      rw [hsum_eq]
    exact h1.trans (le_of_eq h2)
  have hNewPair_facts : ∀ C ∈ newSet, C ∈ components tr.cs.G₀ ∧ C ∉ tr.activeComps := fun C hC => by
    rw [List.mem_toFinset, List.mem_map] at hC; rcases hC with ⟨p, hp, rfl⟩
    obtain ⟨hlt, hnot, _⟩ := hNC_ok p hp; rw [List.getD_eq_getElem y.comps ∅ hlt]
    exact ⟨(hCompsMem _).mp (List.getElem_mem hlt), hnot⟩
  have hnewSlots_sum : ∀ f : ℕ → ℕ, (newSlots.map f).sum =
      newSet.sum fun C => (tr.activeBuckets C).sum fun b => f (slotOf1 (C, b)) := by
    intro f
    have hnewPairs : Finset.image slotOf1 (newSet.biUnion fun C => (tr.activeBuckets C).image (C, ·)) = newSlots.toFinset := by
      ext s; simp only [Finset.mem_image, Finset.mem_biUnion, List.mem_toFinset, hnewSlots_mem]
      constructor
      · rintro ⟨q, ⟨C, hC, b, hb, rfl⟩, rfl⟩
        have hq_mid : (C, b) ∈ activePairs tr_mid := Finset.mem_biUnion.mpr ⟨C, Finset.mem_union_right _ hC, Finset.mem_image_of_mem _ hb⟩
        have hC_not := (hNewPair_facts C hC).2
        have hge : y.slots.length ≤ slotOf1 (C, b) := by
          by_contra hlt; push Not at hlt
          obtain ⟨q0, hq0, hsq0⟩ := hSlotMap0.2.2.1 (slotOf1 (C, b)) (hSlotsRange ▸ List.mem_range.mpr hlt)
          have hq0_mid : q0 ∈ activePairs tr_mid := by
            rcases Finset.mem_biUnion.mp hq0 with ⟨C0, hC0, hb0⟩; exact Finset.mem_biUnion.mpr ⟨C0, Finset.mem_union_left _ hC0, hb0⟩
          have hEq := hSlotMap1.2.2.2.1 (C, b) hq_mid q0 hq0_mid ((hOldSlot1 q0 hq0).trans hsq0).symm
          rcases Finset.mem_biUnion.mp hq0 with ⟨C0, hC0, hb0⟩
          rcases Finset.mem_image.mp hb0 with ⟨b0, _, hq0_eq⟩
          exact hC_not (by have : C = C0 := congrArg Prod.fst (hEq.trans hq0_eq.symm); exact this ▸ hC0)
        exact ⟨hge, List.mem_range.mp (hSlotMap1.2.1 (C, b) hq_mid)⟩
      · rintro ⟨hs_ge, hs_lt⟩
        obtain ⟨q, hq, hsq⟩ := hSlotMap1.2.2.1 s (List.mem_range.mpr hs_lt)
        rcases Finset.mem_biUnion.mp hq with ⟨C, hC, hb⟩
        rcases Finset.mem_image.mp hb with ⟨b, hb_m, rfl⟩
        have hC_new : C ∈ newSet := (Finset.mem_union.mp hC).resolve_left fun hAct => by
          have hq_old : (C, b) ∈ activePairs tr := Finset.mem_biUnion.mpr ⟨C, hAct, Finset.mem_image_of_mem _ hb_m⟩
          have := hOldSlot1 (C, b) hq_old
          have := List.mem_range.mp (hSlotsRange ▸ hSlotMap0.2.1 (C, b) hq_old); omega
        exact ⟨(C, b), ⟨C, hC_new, b, hb_m, rfl⟩, hsq⟩
    rw [← List.sum_toFinset f hnewSlots_nd, ← hnewPairs, Finset.sum_image]
    · rw [Finset.sum_biUnion]
      · refine Finset.sum_congr rfl fun C _ => Finset.sum_image fun b₁ _ b₂ _ h => (Prod.mk.inj h).2
      · intro C₁ _ C₂ _ hne
        refine Finset.disjoint_left.mpr fun q h1 h2 => ?_
        rcases Finset.mem_image.mp h1 with ⟨_, _, rfl⟩; rcases Finset.mem_image.mp h2 with ⟨_, _, hEq⟩
        exact hne (Prod.mk.inj hEq).1.symm
    · intro q₁ hq₁ q₂ hq₂ hEq
      have toMid : ∀ q ∈ newSet.biUnion (fun C => (tr.activeBuckets C).image (C, ·)), q ∈ activePairs tr_mid := fun q hq => by
        rcases Finset.mem_biUnion.mp hq with ⟨C, hC, hb⟩
        exact Finset.mem_biUnion.mpr ⟨C, Finset.mem_union_right _ hC, hb⟩
      exact hSlotMap1.2.2.2.1 q₁ (toMid q₁ hq₁) q₂ (toMid q₂ hq₂) hEq
  have hNewGraph_eq : ∀ C ∈ newSet, ∀ b ∈ tr.activeBuckets C,
      asmFirstInitSlotGraph S1 (slotOf1 (C, b)) = tr.initBunG (C, b) ∧
      SpanGraphOK P (tr.initBunG (C, b)) ∧
      bundleExportCost (slotB S1 (slotOf1 (C, b))) ≤ 100 * (tr.spanConst * spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))) := by
    intro C hC b hb
    obtain ⟨hC_mem, hC_not⟩ := hNewPair_facts C hC
    have hq : (C, b) ∈ activePairs tr_mid := Finset.mem_biUnion.mpr ⟨C, Finset.mem_union_right _ hC, Finset.mem_image_of_mem _ hb⟩
    obtain ⟨hsB, B, hSB, hAg⟩ := hBunMatch1 (C, b) hq
    obtain ⟨_, _, _, _, hLz⟩ := hInactiveInv C hC_mem hC_not
    obtain ⟨_, hInitG, hSpOk⟩ := hLz b hb
    have hGeq : asmFirstInitSlotGraph S1 (slotOf1 (C, b)) = tr.initBunG (C, b) := by
      rw [asmFirstInitSlotGraph, slotB_eq hsB hSB, hInitG]; exact bunAgree_normGraph_eq hAg
    refine ⟨hGeq, hSpOk, ?_⟩
    rw [slotB_eq hsB hSB]
    have hVn : B.vertices.card = (tr.initBunG (C, b)).n := by rw [hInitG]; show B.vertices.card = (normGraph (tr.bun (C, b)).graph).V.card; rw [normGraph_V]; exact congrArg Finset.card hAg.1
    have hEm : B.edges.card = (tr.initBunG (C, b)).m := by rw [hInitG]; show B.edges.card = (normGraph (tr.bun (C, b)).graph).E.card; rw [normGraph_E]; exact congrArg Finset.card hAg.2.1
    have h1 : bundleExportCost B ≤ 100 * ((tr.initBunG (C, b)).n + (tr.initBunG (C, b)).m + 1) := by unfold bundleExportCost; omega
    have h2 := n_add_m_add_one_le_spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))
    have h3 := Nat.le_mul_of_pos_left (spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))) ((one_le_dsAmortConst impl).trans hSpanC)
    exact h1.trans (Nat.mul_le_mul_left 100 (h2.trans h3))
  have hExpSum : (newSlots.map fun s => bundleExportCost (slotB S1 s)).sum ≤ 100 * newSet.sum tr.lazyMachInitCost := by
    rw [hnewSlots_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun C hC => ?_
    exact (Finset.sum_le_sum fun b hb => (hNewGraph_eq C hC b hb).2.2).trans
      (by rw [← Finset.mul_sum]; exact Nat.mul_le_mul_left 100 (hLazyBound C (hNewPair_facts C hC).2))
  have hActSum : (newSlots.map fun s => spanActivateCost P (asmFirstInitSlotGraph S1 s)).sum ≤ newSet.sum tr.lazyMachInitCost := by
    rw [hnewSlots_sum]
    refine Finset.sum_le_sum fun C hC => (Finset.sum_le_sum fun b hb => ?_).trans (hLazyBound C (hNewPair_facts C hC).2)
    obtain ⟨hGeq, hSpOk, _⟩ := hNewGraph_eq C hC b hb
    rw [hGeq]
    have h1 := spanActivateCost_le_spanInitBound P (tr.initBunG (C, b)) hSpOk.2.2.2.2.2.2.1 hSpOk.2.2.2.2.2.2.2.1
    have h2 := spanInitBound_mono (L := depth) hParamsLe (le_of_eq hSplitEq) (tr.initBunG (C, b))
    exact h1.trans (Nat.mul_le_mul hSpanC h2)
  have hBankSum : (newSlots.map fun s => dsInitBank P (asmFirstInitSlotGraph S1 s)).sum ≤ newSet.sum tr.lazyMachInitCost := by
    rw [hnewSlots_sum]
    refine Finset.sum_le_sum fun C hC => ?_
    have hEq : (tr.activeBuckets C).sum (fun b => dsInitBank P (asmFirstInitSlotGraph S1 (slotOf1 (C, b)))) =
        (tr.activeBuckets C).sum (fun b => dsInitBank P (tr.initBunG (C, b))) :=
      Finset.sum_congr rfl fun b hb => by rw [(hNewGraph_eq C hC b hb).1]
    rw [hEq]
    exact newlyActive_initBank_le_lazyMachInitCost P tr C hParamsLe hSpanC (le_of_eq hSplitEq)
      (fun b hb => let hok := (hNewGraph_eq C hC b hb).2.1; ⟨hok.2.2.2.2.2.2.1, hok.2.2.2.2.2.2.2.1⟩)
      (hLazyBound C (hNewPair_facts C hC).2)
  have hNewLen_le : newSlots.length ≤ newSet.sum tr.lazyMachInitCost := by
    have h1 : newSlots.length = (newSlots.map fun _ => 1).sum := by simp
    rw [h1, hnewSlots_sum]
    refine Finset.sum_le_sum fun C hC => (Finset.sum_le_sum fun b hb => ?_).trans (hLazyBound C (hNewPair_facts C hC).2)
    have h2 := n_add_m_add_one_le_spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))
    have h3 := Nat.le_mul_of_pos_left (spanInitBound tr.spanParams depth tr.splitBound (tr.initBunG (C, b))) ((one_le_dsAmortConst impl).trans hSpanC)
    omega
  have hPhiDiff : specPhi P S6' = specPhi P y.spanS + (newSlots.map fun s => dsInitBank P (asmFirstInitSlotGraph S1 s)).sum :=
    specPhi_spanAfter_disj y.spanS (asmFirstInitSlotGraph S1) newSlots hnewSlots_nd
      (fun s hs => (hSlotMap1.2.2.2.2 s (List.mem_range.mpr ((hnewSlots_mem s).mp hs).2)).2)
      (fun s hs hlt_s => hFreeSpan0 ⟨s, hlt_s⟩ (by rw [hSlotsRange]; have := (hnewSlots_mem s).mp hs; simp; omega))
  have hS : cSpan + specPhi P S6' ≤ specPhi P y.spanS +
      (newSlots.map fun s => bundleExportCost (slotB S1 s)).sum +
      (newSlots.map fun s => spanActivateCost P (asmFirstInitSlotGraph S1 s)).sum +
      200 * newSlots.length + 300 := hSpanC_le
  have hK : K * specPhi P S6' ≤ K * specPhi P y.spanS + K * newSet.sum tr.lazyMachInitCost := by
    rw [hPhiDiff, Nat.mul_add]; exact Nat.add_le_add_left (Nat.mul_le_mul_left K hBankSum) _
  have hcSpan : cSpan ≤ 301 * newSet.sum tr.lazyMachInitCost + 300 := by
    rw [hPhiDiff] at hS; omega
  set n := newComps.length
  set sm := newSet.sum tr.lazyMachInitCost
  set lg := ordStoreLog y.eCap5
  have h1 : (rMul + 4 * TS.mul + 3500) * (sm + n) * lg ≤ (rMul + 4 * TS.mul + 3500) * (n + 1 + sm) * lg :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (by omega))
  have h2 : 1000 * (n + 1 + sm) ≤ 1000 * (n + 1 + sm) * lg := Nat.le_mul_of_pos_right _ hlg1
  have h3 : newActCostMul TS rMul * (n + 1 + sm) * lg =
      (rMul + 4 * TS.mul + 3500) * (n + 1 + sm) * lg + 1000 * (n + 1 + sm) * lg := by
    unfold newActCostMul; ring
  omega

end

end MinCostFlow.SparseCore.Program
