module

public import MinCostFlow.SparseCore.Program.AssemblyFirstStepOutEmbRotModel
public import MinCostFlow.SparseCore.Program.AssemblyFirstWalkBound
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepCode
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepPhase1Defs
public import MinCostFlow.SparseCore.Program.AssemblyFirstStepNewActProg

import Mathlib.Tactic

/-!
# Post-step `AsmBrSideModel`, `DSUpdatePre`, and cost telescoping (`AssemblyFirstStepSideStep`)

Completes the side-model and cost-telescoping bridge for Phase 4 and Phase 5 of `AsmBrCoreStepAt`.
It also proves why the side model needs some of its clauses:

1. **Empty batches must be bounded (`gapS9d_empty_batches_genBound_obstruction`)**: appending
   `2 ^ P.w` empty batches `[]` to an active slot's `d.Us` changes none of `d.flat`, `d.state P`,
   `d.G₀`, `∀ u ∈ d.flat, isDelOrSplit u`, or `d.G₀.BatchIsValid d.flat`, yet makes
   `d.genBound P ≥ 2 * 2 ^ P.w > 2 ^ P.w` and falsifies `DSUpdatePre P d' [b, bp, W, h] mem` for
   every `b, bp, W, h, mem`. So the side model must bound the empty batches (`∀ B ∈ d.Us, B ≠ []`).
2. **Single-bundle rotation invariance (`initBundleFor_bunAgree_of_single_root_le`)**:
   when a still-inactive component `C` has `(cs.compSt C).R.card = 1` and
   `2 * E.card ≤ k` (implied by `4 * (compGraph G₀ C).m < k`, proved at init in
   `initTree_inactiveInv`), `initBundleFor cs ord E k` is rotation-invariant (`BunAgree` across any
   `ord`, `ord'`). So `AsmFirstInactiveCompInv` holds under arbitrary trailing `rotateTo` edits.
3. **Full post-step `AsmBrSideModel` preservation (`asmBrSideModel_step`)**:
   proves all 24 conjuncts of `AsmBrSideModel` across `stepBundleTree` under the
   side hypotheses (`y.mMax = tr.m₀`, `2 * eCap + y.splitB + 1 ≤ y.spV`, `eCap ≤ y.spE`,
   `4 * (compGraph tr.cs.G₀ C).m < tr.k` on inactive components, `1 ≤ depth`,
   `1 ≤ max impl.p_s impl.p_t`, and word-size headroom).
4. **Per-slot `DSUpdatePre` derivation (`dsUpdatePre_of_sideModel`)**:
   derives all 10 conjuncts of `DSUpdatePre` for any active slot from `AsmBrSideModel`, the bounds
   (`∀ B ∈ d.Us, B ≠ []`, `y.mMax = tr.m₀`, `2 * eCap + y.splitB + 1 ≤ y.spV`, `eCap ≤ y.spE`) +
   `BranchUpdatesBelow impl info.state (n + U.length)` + word-size headroom.
5. **Unified cost telescoping (`asmFirst_gapS9_reemb_sort_bound`,
   `asmFirst_gapS9_walk_copy_bound`)**:
   proves that raising `asmBrSideRep.phi` to
   `B5.phi + 300 * (capExp + 1) * bundleLogFactor M N * bucketPhi + 300 * walkPot`
   (with `depth ≤ bundleLogFactor M N`) pays all Phase 4 work (P6 updates, `U_H`/`D`/`R` scanning,
   `stepNewWalks` embedding copies including `142 * depth` per `R_p ∪ L_p` edge, and sorting
   `stepBundleTree_reembList`) cleanly against `branchStepCharge + (words + editWords + 1) * lg`.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.Chain MinCostFlow.SparseCore MinCostFlow.LSF
open MinCostFlow.DynSpanner MinCostFlow.DynSpanner.Program MinCostFlow.MinRatio
open MinCostFlow.SparseCore.Program.Restart

public section

/-! ## 1. Empty batches must be bounded -/

/-- **Empty batches must be bounded**: appending `2 ^ P.w` empty batches `[]` to `d.Us` preserves every
`DSHist` field constrained by `AsmBrSideModel` (`d'.flat = d.flat`, `d'.state P = d.state P`,
`d'.G₀ = d.G₀`), yet makes `d'.genBound P ≥ 2 * 2 ^ P.w` and falsifies `DSUpdatePre` for every
update call. So a side model must bound `d.Us.length` (for example by `∀ B ∈ d.Us, B ≠ []`). -/
theorem gapS9d_empty_batches_genBound_obstruction (P : DSParams) (d : DSHist) :
    let d' : DSHist := ⟨d.G₀, d.Us ++ List.replicate (2 ^ P.w) []⟩
    d'.flat = d.flat ∧
    d'.state P = d.state P ∧
    d'.G₀ = d.G₀ ∧
    (∀ b batchPtr W h mem, ¬ DSUpdatePre P d' [b, batchPtr, W, h] mem) := by
  intro d'
  have hflat : d'.flat = d.flat := by
    simp [d', DSHist.flat, List.flatten_append]
  refine ⟨hflat, ?_, rfl, ?_⟩
  · simp [DSHist.state, DSHist.q, hflat, d']
  · intro b batchPtr W h mem hpre
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hgen, _, _, _⟩ := hpre
    have hge : 2 * 2 ^ P.w ≤ d'.genBound P := by
      simp only [DSHist.genBound, d', List.length_append, List.length_replicate]
      omega
    omega

/-! ## 2. Single-bundle rotation invariance for small inactive components -/

private lemma initialChunks_eq_singleton_of_le {α : Type*} {k : ℕ} {xs : List α}
    (hk : 0 < k) (hne : xs ≠ []) (hle : xs.length ≤ k) :
    initialChunks k xs = [xs] := by
  have hpos : 0 < xs.length := List.length_pos_of_ne_nil hne
  have hcd : xs.length ⌈/⌉ k = 1 := by
    rw [Nat.ceilDiv_eq_add_pred_div]
    have h1 : 1 * k ≤ xs.length + k - 1 := by omega
    have h2 : xs.length + k - 1 < (1 + 1) * k := by omega
    exact Nat.div_eq_of_lt_le h1 h2
  have hlen : (initialChunks k xs).length = 1 := by rw [initialChunks_length, hcd]
  have hfl : (initialChunks k xs).flatten = xs := (initialChunks_spec hk xs).1
  cases h : initialChunks k xs with
  | nil => simp [h] at hlen
  | cons a rest =>
    cases rest with
    | nil => simpa [h] using hfl
    | cons _ _ => simp [h] at hlen

private lemma initialSlots_single_root_eq {C : MGraph} (ρ : Rotation C) (hC : C.IsValid)
    {E : Finset ℕ} (hE : E ⊆ C.E) {r k : ℕ} (hk : 0 < k) (hEne : E.Nonempty)
    (hsrc : ∀ e ∈ E, C.tail e = r ∧ C.head e = r) (hsize : 2 * E.card ≤ k) :
    initialSlots ρ E k = [(r, restrictedEnds ρ E r)] := by
  obtain ⟨e₀, he₀⟩ := hEne
  have hrV : r ∈ C.V := (hsrc e₀ he₀).1 ▸ (hC e₀ (hE he₀)).1
  have hres_nil : ∀ v ∈ C.V, v ≠ r → restrictedEnds ρ E v = [] := by
    intro v _ hne
    rw [List.eq_nil_iff_forall_not_mem]
    intro x hx
    obtain ⟨hxE, hxsrc⟩ := (mem_restrictedEnds ρ hE v x).mp hx
    have hxr : C.src x = r := by cases hx2 : x.2 <;> simp [MGraph.src, hx2, (hsrc x.1 hxE).1, (hsrc x.1 hxE).2]
    exact hne (hxsrc.symm.trans hxr)
  have hres_ne : restrictedEnds ρ E r ≠ [] := by
    intro hnil
    have hm : (e₀, true) ∈ restrictedEnds ρ E r :=
      (mem_restrictedEnds ρ hE r (e₀, true)).mpr ⟨he₀, (hsrc e₀ he₀).1⟩
    rw [hnil] at hm; cases hm
  have hres_len : (restrictedEnds ρ E r).length ≤ k := by
    have hnd : (restrictedEnds ρ E r).Nodup := (ρ.nodup r).filter _
    have hsub : (restrictedEnds ρ E r).toFinset ⊆ E ×ˢ ({true, false} : Finset Bool) := by
      intro x hx
      have hm := (mem_restrictedEnds ρ hE r x).mp (List.mem_toFinset.mp hx)
      exact Finset.mem_product.mpr ⟨hm.1, by cases x.2 <;> simp⟩
    have hcard : (restrictedEnds ρ E r).length ≤ (E ×ˢ ({true, false} : Finset Bool)).card := by
      rw [← List.toFinset_card_of_nodup hnd]; exact Finset.card_le_card hsub
    rw [Finset.card_product] at hcard
    have h2 : ({true, false} : Finset Bool).card = 2 := by decide
    rw [h2] at hcard; omega
  have hchunks_ne : ∀ v ∈ C.V, v ≠ r → initialChunks k (restrictedEnds ρ E v) = [] := by
    intro v hv hne
    rw [hres_nil v hv hne, List.eq_nil_iff_length_eq_zero, initialChunks_length]
    simp
  have hchunks_r : initialChunks k (restrictedEnds ρ E r) = [restrictedEnds ρ E r] :=
    initialChunks_eq_singleton_of_le hk hres_ne hres_len
  unfold initialSlots
  have hsort_mem : r ∈ C.V.sort (· ≤ ·) := (Finset.mem_sort _).mpr hrV
  have hsort_nd : (C.V.sort (· ≤ ·)).Nodup := Finset.sort_nodup _ _
  have hflat : ∀ (L : List ℕ), L.Nodup → (∀ v ∈ L, v ∈ C.V) → r ∈ L →
      L.flatMap (fun v => (initialChunks k (restrictedEnds ρ E v)).map (v, ·)) =
        [(r, restrictedEnds ρ E r)] := by
    intro L; induction L with
    | nil => intro _ _ h; cases h
    | cons a rest ih =>
      intro hnd hsub hmem
      rcases List.nodup_cons.mp hnd with ⟨ha_nmem, hnd_r⟩
      rcases List.mem_cons.mp hmem with rfl | hmem_r
      · simp only [List.flatMap_cons, hchunks_r, List.map_singleton, List.singleton_append]
        have hrest_nil : rest.flatMap (fun v => (initialChunks k (restrictedEnds ρ E v)).map (v, ·)) = [] := by
          rw [List.flatMap_eq_nil_iff]
          intro v hv
          have hne : v ≠ r := fun h => ha_nmem (h ▸ hv)
          rw [hchunks_ne v (hsub v (List.mem_cons_of_mem _ hv)) hne]; rfl
        rw [hrest_nil]
      · have hne : a ≠ r := fun h => ha_nmem (h ▸ hmem_r)
        simp only [List.flatMap_cons, hchunks_ne a (hsub a List.mem_cons_self) hne, List.map_nil, List.nil_append]
        exact ih hnd_r (fun v hv => hsub v (List.mem_cons_of_mem _ hv)) hmem_r
  exact hflat (C.V.sort (· ≤ ·)) hsort_nd (fun v hv => (Finset.mem_sort _).mp hv) hsort_mem

private lemma initBundleState_single_bunAgree {C₁ C₂ : MGraph}
    (ρ₁ : Rotation C₁) (ρ₂ : Rotation C₂) {E : Finset ℕ} {r k : ℕ}
    {ys₁ ys₂ : List End}
    (hs₁ : initialSlots ρ₁ E k = [(r, ys₁)]) (hs₂ : initialSlots ρ₂ E k = [(r, ys₂)])
    (hm₁ : ∀ x : End, x.1 ∈ E → x ∈ ys₁) (hm₂ : ∀ x : End, x.1 ∈ E → x ∈ ys₂) :
    BunAgree (initBundleState ρ₁ E k) (initBundleState ρ₂ E k) := by
  refine ⟨by simp [initBundleState, hs₁, hs₂], rfl, ?_, fun x hx => ?_⟩
  · funext b; simp [initBundleState, hs₁, hs₂]; cases b <;> simp
  · simp [initBundleState, hs₁, hs₂, List.findIdx, List.findIdx.go, hm₁ x hx, hm₂ x hx]

private lemma initBundleState_empty_bunAgree {C₁ C₂ : MGraph}
    (ρ₁ : Rotation C₁) (ρ₂ : Rotation C₂) {k : ℕ}
    (hs₁ : initialSlots ρ₁ ∅ k = []) (hs₂ : initialSlots ρ₂ ∅ k = []) :
    BunAgree (initBundleState ρ₁ ∅ k) (initBundleState ρ₂ ∅ k) :=
  ⟨by simp [initBundleState, hs₁, hs₂], rfl,
   by funext b; simp [initBundleState, hs₁, hs₂], fun _ hx => by cases hx⟩

/-- **Single-bundle rotation invariance**: if every edge of `E` has both endpoints at a
single root `r` in both `coreGraph cs₁.G cs₁.lsf` and `coreGraph cs₂.G cs₂.lsf`, and
`2 * E.card ≤ k` (`0 < k`), then `initBundleFor cs₁ ord₁ E k` and `initBundleFor cs₂ ord₂ E k`
agree (`BunAgree`) for **arbitrary** rotation orders `ord₁`, `ord₂`. -/
theorem initBundleFor_bunAgree_of_single_root_le
    {C₁ C₂ : ℝ} {ℓ₁ ℓ₂ : ℕ → ℝ} {cs₁ cs₂ : CompLSFState}
    {ord₁ ord₂ : ℕ → List End} {E : Finset ℕ} {r k : ℕ}
    (hI₁ : CompLSFInv C₁ ℓ₁ cs₁) (hI₂ : CompLSFInv C₂ ℓ₂ cs₂)
    (ρ₁ : Rotation cs₁.G) (hρ₁ : ρ₁.order = ord₁)
    (ρ₂ : Rotation cs₂.G) (hρ₂ : ρ₂.order = ord₂)
    (hE₁ : E ⊆ (coreGraph cs₁.G cs₁.lsf).E) (hE₂ : E ⊆ (coreGraph cs₂.G cs₂.lsf).E)
    (hsrc₁ : ∀ e ∈ E, (coreGraph cs₁.G cs₁.lsf).tail e = r ∧ (coreGraph cs₁.G cs₁.lsf).head e = r)
    (hsrc₂ : ∀ e ∈ E, (coreGraph cs₂.G cs₂.lsf).tail e = r ∧ (coreGraph cs₂.G cs₂.lsf).head e = r)
    (hk : 0 < k) (hsize : 2 * E.card ≤ k) :
    BunAgree (initBundleFor cs₁ ord₁ E k) (initBundleFor cs₂ ord₂ E k) := by
  rw [initBundleFor_eq hI₁ hρ₁ E k, initBundleFor_eq hI₂ hρ₂ E k]
  set ρc₁ := coreRotation (L := cs₁.lsf) ρ₁ hI₁.hG_val (compLSF_RF_isRSF hI₁)
  set ρc₂ := coreRotation (L := cs₂.lsf) ρ₂ hI₂.hG_val (compLSF_RF_isRSF hI₂)
  by_cases hEne : E.Nonempty
  · have hC₁ : (coreGraph cs₁.G cs₁.lsf).IsValid := coreGraph_isValid hI₁.hG_val (compLSF_RF_isRSF hI₁)
    have hC₂ : (coreGraph cs₂.G cs₂.lsf).IsValid := coreGraph_isValid hI₂.hG_val (compLSF_RF_isRSF hI₂)
    exact initBundleState_single_bunAgree ρc₁ ρc₂
      (initialSlots_single_root_eq ρc₁ hC₁ hE₁ hk hEne hsrc₁ hsize)
      (initialSlots_single_root_eq ρc₂ hC₂ hE₂ hk hEne hsrc₂ hsize)
      (fun x hx => (mem_restrictedEnds ρc₁ hE₁ r x).mpr
        ⟨hx, by cases hx2 : x.2 <;> simp [MGraph.src, hx2, (hsrc₁ x.1 hx).1, (hsrc₁ x.1 hx).2]⟩)
      (fun x hx => (mem_restrictedEnds ρc₂ hE₂ r x).mpr
        ⟨hx, by cases hx2 : x.2 <;> simp [MGraph.src, hx2, (hsrc₂ x.1 hx).1, (hsrc₂ x.1 hx).2]⟩)
  · rw [Finset.not_nonempty_iff_eq_empty] at hEne; subst hEne
    have hslot_nil : ∀ (C : MGraph) (ρ : Rotation C), initialSlots ρ ∅ k = [] := by
      intro C ρ; unfold initialSlots
      rw [List.flatMap_eq_nil_iff]; intro v _
      have hnil : restrictedEnds ρ ∅ v = [] := by simp [restrictedEnds]
      rw [hnil, List.map_eq_nil_iff, List.eq_nil_iff_length_eq_zero, initialChunks_length]; simp
    exact initBundleState_empty_bunAgree ρc₁ ρc₂ (hslot_nil _ ρc₁) (hslot_nil _ ρc₂)

/-! ## 3. Step preservation for `AsmFirstInactiveCompInv` and `SpanGraphOK` -/

private lemma mem_RF_F_E_iff_local (cs : CompLSFState) (e : ℕ) :
    e ∈ cs.RF.F.E ↔ ∃ C ∈ components cs.G₀, e ∈ (cs.compSt C).RF.F.E := by
  change e ∈ (components cs.G₀).biUnion (fun C => (cs.compSt C).RF.F.E) ↔ _
  exact Finset.mem_biUnion

private lemma coreGraph_tail_in_comp_eq {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    {C : Finset ℕ} (hI : CompLSFInv C_lsst ℓ₀ cs) (hC : C ∈ components cs.G₀)
    (hR1 : (cs.compSt C).R.card = 1)
    (hCr : Disjoint (cs.compSt C).G.E cs.crossEdges ∧
      ∀ e ∈ cs.crossEdges, cs.G.tail e ∉ (cs.compSt C).G.V ∧ cs.G.head e ∉ (cs.compSt C).G.V) :
    ((coreGraph cs.G cs.lsf).E.filter fun e => (coreGraph cs.G cs.lsf).tail e ∈ C) =
      (cs.compSt C).G.E \ (cs.compSt C).RF.F.E := by
  have hCsubV : C ⊆ (cs.compSt C).G.V := by
    have hLC := (hI.hCompLSF C hC).1
    have hG0C := (hI.hCompLSF C hC).2.1
    intro u hu; rw [hLC.hGV_eq]; exact Finset.mem_union_left _ (hLC.hTV.symm ▸ (hG0C.symm ▸ hu))
  ext e
  simp only [Finset.mem_filter, Finset.mem_sdiff]
  constructor
  · rintro ⟨heCore, htC⟩
    obtain ⟨heG, hneF⟩ := Finset.mem_sdiff.mp heCore
    have htV : cs.G.tail e ∈ (cs.compSt C).G.V :=
      compLSF_mem_V_of_root hI hC (hI.hG_val e heG).1 (hCsubV htC)
    have hnc : e ∉ cs.crossEdges := fun hcr => (hCr.2 e hcr).1 htV
    obtain ⟨C', hC', heC'⟩ := hI.hEdge_cover e heG hnc
    have hends := hI.hNonCross_ends C' hC' e heC' hnc
    have hvC' := (hI.hCompLSF C' hC').1.hG_val e heC'
    have hCC : C' = C := by
      by_contra hne
      exact Finset.disjoint_left.mp (hI.hV_disj C' hC' C hC hne) (hends.1 ▸ hvC'.1) htV
    exact ⟨hCC ▸ heC', fun hF => hneF ((mem_RF_F_E_iff_local cs e).mpr ⟨C, hC, hF⟩)⟩
  · rintro ⟨heC, hnfC⟩
    have heG : e ∈ cs.G.E := hI.hCE_sub C hC heC
    have hnc : e ∉ cs.crossEdges := Finset.disjoint_left.mp hCr.1 heC
    have hends := hI.hNonCross_ends C hC e heC hnc
    have htC_v : cs.G.tail e ∈ (cs.compSt C).G.V := hends.1 ▸ ((hI.hCompLSF C hC).1.hG_val e heC).1
    have huniq := inactive_comp_root_unique hI hC hR1 htC_v
    have hrtC : (coreGraph cs.G cs.lsf).tail e ∈ C := huniq.2.1
    refine ⟨Finset.mem_sdiff.mpr ⟨heG, fun hF => ?_⟩, hrtC⟩
    obtain ⟨C', hC', heF'⟩ := (mem_RF_F_E_iff_local cs e).mp hF
    by_cases hCC : C' = C
    · exact hnfC (hCC ▸ heF')
    · have heC' := (hI.hCompLSF C' hC').1.hF_sub_G.2.1 heF'
      have hends' := hI.hNonCross_ends C' hC' e heC' hnc
      exact Finset.disjoint_left.mp (hI.hV_disj C hC C' hC' (Ne.symm hCC)) htC_v
        (hends'.1 ▸ ((hI.hCompLSF C' hC').1.hG_val e heC').1)

/-- **`AsmFirstInactiveCompInv` across `stepBundleTree`**. -/
theorem asmFirstInactiveCompInv_step
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth : ℕ} {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ}
    (sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut)
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    {y y' : AsmBrSide B5 depth}
    (hSP : asmBrSP impl w depth y' = asmBrSP impl w depth y)
    (hI : CompLSFInv C_lsst ℓ₀ tr.cs) (hU : tr.cs.G.BatchIsValid U)
    (hOB : OrderedBatch tr.cs.G U ord ord') (hk : 1 ≤ tr.k)
    (hInact : AsmFirstInactiveCompInv impl w depth tr ord y)
    (hCross : AsmFirstCrossInactiveInv tr) :
    AsmFirstInactiveCompInv impl w depth (stepBundleTree sp tr U ord ord').state ord' y' := by
  classical
  set info := stepBundleTree sp tr U ord ord'
  set tr' := info.state
  have hI' := compLSFBatch_inv hI hU
  have hCross' := asmFirstCrossInactiveInv_step (ord := ord) (ord' := ord') sp hI hU hCross
  obtain ⟨ρ, σ, hρ, hσ, hRB⟩ := hOB
  intro C hC' hnotA'
  have hC0 : C ∈ components tr.cs.G₀ := by simpa [tr', info, stepBundleTree, compLSFBatch_G₀] using hC'
  have hnotA : C ∉ tr.activeComps := fun h => hnotA' (Finset.mem_union_left _ h)
  have hnotT : C ∉ touchedCompsBatch tr.cs U := fun h =>
    hnotA' (Finset.mem_union_right _ (Finset.mem_sdiff.mpr ⟨h, hnotA⟩))
  have hunt := (compLSFBatch_untouched hI hU hC0 hnotT).2
  have hInC := hInact C hC0 hnotA
  have hcs' : tr'.cs = compLSFBatch tr.cs U := rfl
  have hG0' : tr'.cs.G₀ = tr.cs.G₀ := compLSFBatch_G₀ tr.cs U
  have hR1' : (tr'.cs.compSt C).R.card = 1 := by rw [hcs', hunt]; exact hInC.1
  have hSmall' : 4 * (tr'.cs.compSt C).G.m < tr'.k := by
    change 4 * ((compLSFBatch tr.cs U).compSt C).G.m < tr.k
    rw [hunt]; exact hInC.2.2.2.1
  have hEeq0 := coreGraph_tail_in_comp_eq hI hC0 hInC.1 (hCross C hC0 hnotA)
  have hEeq1 := coreGraph_tail_in_comp_eq hI' hC' (hcs' ▸ hR1') (hCross' C hC' hnotA')
  have hCoreEq : ((coreGraph tr'.cs.G tr'.cs.lsf).E.filter fun e =>
      (coreGraph tr'.cs.G tr'.cs.lsf).tail e ∈ C) =
      ((coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
        (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C) := by
    rw [hcs', hEeq1, hEeq0, hunt]
  refine ⟨hR1', ?_, ?_, hSmall', ?_⟩
  · change tr.activeBuckets C = _; rw [hCoreEq]; exact hInC.2.1
  · intro e he htC
    have hm : e ∈ (coreGraph tr.cs.G tr.cs.lsf).E.filter fun e =>
        (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C := by
      rw [← hCoreEq]; exact Finset.mem_filter.mpr ⟨he, htC⟩
    have hm' := Finset.mem_filter.mp hm
    rw [hG0']; exact hInC.2.2.1 e hm'.1 hm'.2
  · intro b hb
    have hReady := inactive_bundleCompReady hI hk hInact hCross hC0 hnotA hb
    have hStage := bundleCompStep_stage hI hU hρ hσ hRB hC0 hReady
    have hBunEq : tr'.bun (C, b) = tr.bun (C, b) := by
      change (bundleCompStep tr.cs (tr.bun (C, b)) tr.k ord ord' U).2 = _
      rw [hStage.2.2.2.2.2.2.2.2 hnotT]
    have hEq_same : bucketCoreEdges (coreGraph tr'.cs.G tr'.cs.lsf) tr'.origBucket C b =
        bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b := by
      ext e; simp only [bucketCoreEdges, Finset.mem_filter]
      have hiff : (e ∈ (coreGraph tr'.cs.G tr'.cs.lsf).E ∧ (coreGraph tr'.cs.G tr'.cs.lsf).tail e ∈ C) ↔
          (e ∈ (coreGraph tr.cs.G tr.cs.lsf).E ∧ (coreGraph tr.cs.G tr.cs.lsf).tail e ∈ C) := by
        simpa [Finset.mem_filter] using congrArg (e ∈ ·) hCoreEq
      change (e ∈ (coreGraph tr'.cs.G tr'.cs.lsf).E ∧ (coreGraph tr'.cs.G tr'.cs.lsf).tail e ∈ C ∧
        tr.origBucket e = b) ↔ _
      exact ⟨fun ⟨h1, h2, h3⟩ => let ⟨a, b⟩ := hiff.mp ⟨h1, h2⟩; ⟨a, b, h3⟩,
        fun ⟨h1, h2, h3⟩ => let ⟨a, b⟩ := hiff.mpr ⟨h1, h2⟩; ⟨a, b, h3⟩⟩
    obtain ⟨r, hrR⟩ := Finset.card_eq_one.mp hInC.1
    have hrR' : (tr'.cs.compSt C).R = {r} := by rw [hcs', hunt, hrR]
    set Eq := bucketCoreEdges (coreGraph tr.cs.G tr.cs.lsf) tr.origBucket C b
    have hEq_sub_C : Eq ⊆ (tr.cs.compSt C).G.E \ (tr.cs.compSt C).RF.F.E := by
      rw [← hEeq0]; intro e he
      have hm := Finset.mem_filter.mp he; exact Finset.mem_filter.mpr ⟨hm.1, hm.2.1⟩
    have hEq_card : 2 * Eq.card ≤ tr.k := by
      have hle : Eq.card ≤ (tr.cs.compSt C).G.m :=
        Finset.card_le_card (hEq_sub_C.trans Finset.sdiff_subset)
      have hsm := hInC.2.2.2.1
      omega
    have hsrc0 : ∀ e ∈ Eq, (coreGraph tr.cs.G tr.cs.lsf).tail e = r ∧
        (coreGraph tr.cs.G tr.cs.lsf).head e = r := by
      intro e he
      have heC := (Finset.mem_sdiff.mp (hEq_sub_C he)).1
      have hnc := Finset.disjoint_left.mp (hCross C hC0 hnotA).1 heC
      have hends := hI.hNonCross_ends C hC0 e heC hnc
      have hvC := (hI.hCompLSF C hC0).1.hG_val e heC
      have ht : tr.cs.RF.root (tr.cs.G.tail e) = r := by
        have hmem := compLSF_root_mem_R hI hC0 (hends.1 ▸ hvC.1)
        exact Finset.mem_singleton.mp (hrR ▸ hmem)
      have hh : tr.cs.RF.root (tr.cs.G.head e) = r := by
        have hmem := compLSF_root_mem_R hI hC0 (hends.2 ▸ hvC.2)
        exact Finset.mem_singleton.mp (hrR ▸ hmem)
      exact ⟨ht, hh⟩
    have hsrc1 : ∀ e ∈ Eq, (coreGraph tr'.cs.G tr'.cs.lsf).tail e = r ∧
        (coreGraph tr'.cs.G tr'.cs.lsf).head e = r := by
      intro e he
      have heC' : e ∈ (tr'.cs.compSt C).G.E := by
        change e ∈ ((compLSFBatch tr.cs U).compSt C).G.E; rw [hunt]; exact (Finset.mem_sdiff.mp (hEq_sub_C he)).1
      have hnc' := Finset.disjoint_left.mp (hCross' C hC' hnotA').1 heC'
      have hends' := hI'.hNonCross_ends C hC' e heC' hnc'
      have hvC' := (hI'.hCompLSF C hC').1.hG_val e heC'
      have ht : tr'.cs.RF.root (tr'.cs.G.tail e) = r := by
        have hmem := compLSF_root_mem_R hI' hC' (hends'.1 ▸ hvC'.1)
        exact Finset.mem_singleton.mp (hrR' ▸ hmem)
      have hh : tr'.cs.RF.root (tr'.cs.G.head e) = r := by
        have hmem := compLSF_root_mem_R hI' hC' (hends'.2 ▸ hvC'.2)
        exact Finset.mem_singleton.mp (hrR' ▸ hmem)
      exact ⟨ht, hh⟩
    have hG_eq_cs' : tr.cs.G.applyBatch U = (compLSFBatch tr.cs U).G := (compLSFBatch_G tr.cs U).symm
    let σ' : Rotation (compLSFBatch tr.cs U).G := hG_eq_cs' ▸ σ
    have hσ' : σ'.order = ord' := by
      have hord_cast : ∀ {G₁ G₂ : MGraph} (heq : G₁ = G₂) (r : Rotation G₁), (heq ▸ r).order = r.order := by
        rintro G₁ _ rfl _; rfl
      exact (hord_cast hG_eq_cs' σ).trans hσ
    have hEq_sub_core' : Eq ⊆ (coreGraph (compLSFBatch tr.cs U).G (compLSFBatch tr.cs U).lsf).E := by
      rw [← hEq_same]; exact bucketCoreEdges_sub_coreE _ _ _ _
    have hAg1 := initBundleFor_bunAgree_of_single_root_le hI' hI σ' hσ'
      ρ hρ hEq_sub_core' (bucketCoreEdges_sub_coreE _ _ _ _)
      hsrc1 hsrc0 hk hEq_card
    have hAg0 := (hInC.2.2.2.2 b hb).1
    refine ⟨?_, ?_, ?_⟩
    · rw [hEq_same, hBunEq]
      exact ⟨hAg1.1.trans hAg0.1, hAg1.2.1.trans hAg0.2.1, hAg1.2.2.1.trans hAg0.2.2.1,
        fun x hx => (hAg1.2.2.2 x hx).trans (hAg0.2.2.2 x (hAg1.2.1 ▸ hx))⟩
    · rw [hBunEq]; exact (hInC.2.2.2.2 b hb).2.1
    · rw [hSP]; exact (hInC.2.2.2.2 b hb).2.2

/-- **`SpanGraphOK` for `restartSlotGraph` after a step**, under the parameter bounds
(`y.mMax = tr.m₀`, `2 * eCap + y.splitB + 1 ≤ y.spV`, `eCap ≤ y.spE`) and word-size headroom. -/
theorem restartSlotGraph_spanGraphOK_step
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth vCap eCap : ℕ}
    {tr' : BundleTreeState depth} {ord' : ℕ → List End} {y' : AsmBrSide B5 depth}
    (hF' : AsmBrModelFacts impl vCap eCap tr' ord')
    (hMap' : SlotMapOK tr' y'.slotCap y'.cap y'.slots y'.slotOf)
    (hMatch' : BunTableMatches tr' y'.slotOf y'.bunS)
    (hPart' : AsmFirstActiveBunPartInv tr' ord')
    (hBUB' : ∀ C ∈ components tr'.cs.G₀, ∀ b, (tr'.initBunG (C, b)).m ≤ tr'.m₀)
    (hBunSubInit : ∀ p ∈ activePairs tr', (tr'.bun p).edges.card ≤ (tr'.initBunG p).m)
    (hmMax : y'.mMax = tr'.m₀)
    (hspV : 2 * eCap + y'.splitB + 1 ≤ y'.spV) (hspE : eCap ≤ y'.spE)
    (hL : 1 ≤ depth) (hp : 1 ≤ max impl.p_s impl.p_t) (hw16 : 16 ≤ 2 ^ w)
    (hw : y'.spV + y'.spE + 2 < 2 ^ w)
    (hcw : (36 * (y'.spV + 2 * y'.spE + 1)) ^ impl.cw < 2 ^ w) :
    ∀ s ∈ y'.slots, SpanGraphOK (asmBrSP impl w depth y')
      (restartSlotGraph y'.bunS tr'.cs ord' tr'.k s) := by
  classical
  intro s hs
  set P := asmBrSP impl w depth y'
  obtain ⟨hk, ⟨C_lsst, ℓ₀, hI', ρ', hρ'⟩, hMod', -, -, -, -, -, heCapG', -⟩ := hF'
  obtain ⟨q, hq, hsq⟩ := hMap'.2.2.1 s hs
  obtain ⟨hsB, B, hSB, hAg⟩ := hMatch' q hq
  have hs_lt : s < y'.slotCap := hsq ▸ hsB
  have hS_s : y'.bunS ⟨s, hs_lt⟩ = some B := by convert hSB using 2; exact Fin.ext hsq.symm
  have hB_edges : B.edges = (tr'.bun q).edges := hAg.2.1
  have hqC : q.1 ∈ tr'.activeComps := (mem_activePairs.mp hq).1
  have hqb : q.2 ∈ tr'.activeBuckets q.1 := (mem_activePairs.mp hq).2
  have hEcore : B.edges ⊆ (coreGraph tr'.cs.G tr'.cs.lsf).E := by
    rw [hB_edges]; exact (hPart' q.1 hqC q.2 hqb C_lsst ℓ₀ hI' ρ' hρ').1
  have hEG : B.edges ⊆ tr'.cs.G.E := fun e he => (Finset.mem_sdiff.mp (hEcore he)).1
  set Br := initBundleFor tr'.cs ord' B.edges tr'.k
  have hgr : restartSlotGraph y'.bunS tr'.cs ord' tr'.k s = Restart.normGraph Br.graph := by
    simp [restartSlotGraph, restartSlotBundle, hs_lt, hS_s, Br]
  have hval : Br.graph.IsValid := initBundleFor_graph_isValid hEcore hk
  have hBE : Br.edges ⊆ B.edges := initBundleFor_edges_subset _ _ _ _
  have hEcard : B.edges.card ≤ eCap := by
    calc B.edges.card ≤ (Finset.range eCap).card :=
          Finset.card_le_card fun e he => Finset.mem_range.mpr (heCapG' e (hEG he))
      _ = eCap := Finset.card_range _
  have hn : Br.vertices.card ≤ 2 * B.edges.card := initBundleFor_vertices_le_two_card hEcore hk
  have hvlt : ∀ v ∈ Br.vertices, v < 2 * eCap := by
    intro v hv
    have hr : Br.vertices = Finset.range Br.vertices.card :=
      initBundleFor_vertices_range tr'.cs ord' B.edges tr'.k
    rw [hr] at hv
    have := Finset.mem_range.mp hv; omega
  have hmB : Br.edges.card ≤ B.edges.card := Finset.card_le_card hBE
  have hmM : B.edges.card ≤ y'.mMax := by
    rw [hB_edges, hmMax]
    exact (hBunSubInit q hq).trans (hBUB' q.1 (hMod'.1 hqC) q.2)
  have hGn : (Restart.normGraph Br.graph).n = Br.vertices.card := rfl
  have hGm : (Restart.normGraph Br.graph).m = Br.edges.card := rfl
  have hvalN : (Restart.normGraph Br.graph).IsValid := by
    intro e he
    have he' : e ∈ Br.graph.E := he
    have hve := hval e he'
    exact ⟨by simp [Restart.normGraph, he', hve.1], by simp [Restart.normGraph, he', hve.2]⟩
  rw [hgr]
  refine ⟨hL, hp, hw16, by change (Restart.normGraph Br.graph).n + y'.splitB + 2 < 2 ^ w; rw [hGn]; omega,
    by change 1 + (Restart.normGraph Br.graph).m < 2 ^ w; rw [hGm]; omega, fun _ => ?_,
    hvalN,
    by change (Restart.normGraph Br.graph).m ≤ y'.mMax; rw [hGm]; omega,
    fun v hv => lt_of_lt_of_le (hvlt v hv) (by change 2 * eCap ≤ y'.spV; omega),
    fun e he => lt_of_lt_of_le (heCapG' e (hEG (hBE he))) hspE⟩
  refine le_trans (wordSize_canonSparsifyInput_id_le _ _ hvalN)
    (mul_log_succ_le_of_pow_lt (by omega) ?_)
  have hact := activeSubgraph_n_le (Restart.normGraph Br.graph)
  refine lt_of_le_of_lt (Nat.pow_le_pow_left ?_ _) hcw
  have hm_act : (activeSubgraph (Restart.normGraph Br.graph)).m = Br.edges.card := rfl
  omega

/-! ## 4. Full post-step `AsmBrSideModel` preservation (`asmBrSideModel_step`) -/

/-- **Full preservation of `AsmBrSideModel` across `stepBundleTree`**, given the side
hypotheses (`y.mMax = tr.m₀`, `2 * eCap + y.splitB + 1 ≤ y.spV`, `eCap ≤ y.spE`,
`4 * (compGraph tr.cs.G₀ C).m < tr.k` on inactive components, `1 ≤ depth`,
`1 ≤ max impl.p_s impl.p_t`, and word-size headroom). -/
theorem asmBrSideModel_step
    {B5 : (kB slotCap vCap eCap : ℕ) → DSRep (Fin slotCap → Option BundleState)}
    {impl : SparsifyImpl} {w depth L capExp limbMul vCap eCap n : ℕ}
    {Ψ : BundleTreeState depth → ℕ}
    {tr : BundleTreeState depth} {U : List Update} {ord ord' : ℕ → List End}
    {y y' : AsmBrSide B5 depth}
    (hSide : AsmBrSideModel impl w depth L capExp limbMul Ψ ⟨tr, ord, vCap, eCap⟩ y)
    (hF' : AsmBrModelFacts impl vCap eCap
      (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state ord')
    (hBUB' : BranchUpdatesBelow impl
      (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state (n + U.length))
    (hU : tr.cs.G.BatchIsValid U) (hOB : OrderedBatch tr.cs.G U ord ord')
    -- Unchanged parameter fields between `y` and `y'`
    (hkB : y'.kB = y.kB) (hsplitB : y'.splitB = y.splitB)
    (hspV_eq : y'.spV = y.spV) (hspE_eq : y'.spE = y.spE) (hmMax_eq : y'.mMax = y.mMax)
    (hlgFac_eq : y'.lgFac = y.lgFac)
    -- Phase 2 / 3 / 4 outputs on `y'`
    (hMap' : SlotMapOK (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state
      y'.slotCap y'.cap y'.slots y'.slotOf)
    (hMatch' : BunTableMatches (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state
      y'.slotOf y'.bunS)
    (hSpan' : ∀ q ∈ activePairs (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state,
      ∃ (hs : y'.slotOf q < y'.cap) (d : DSHist),
        y'.spanS ⟨y'.slotOf q, hs⟩ = some d ∧
        d.state (asmBrSP impl w depth y') =
          (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state.dyn q ∧
        d.G₀ = (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state.initBunG q ∧
        (∀ u ∈ d.flat, isDelOrSplit u) ∧ d.G₀.BatchIsValid d.flat ∧ (∀ B ∈ d.Us, B ≠ []))
    (hBunInv' : bunRestartInv vCap eCap y'.bunS
      (outCoreOrder (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state ord'))
    (hWP' : y'.walkPot = Ψ (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state)
    (hSlotInv' : AsmFirstSideSlotInv
      (stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state y')
    -- Word-size headroom
    (hL : 1 ≤ depth) (hp : 1 ≤ max impl.p_s impl.p_t) (hw16 : 16 ≤ 2 ^ w)
    (hw : y.spV + y.spE + 2 < 2 ^ w)
    (hcw : (36 * (y.spV + 2 * y.spE + 1)) ^ impl.cw < 2 ^ w) :
    AsmBrSideModel impl w depth L capExp limbMul Ψ
      ⟨(stepBundleTree (fun _ => canonicalSparsify impl) tr U ord ord').state, ord', vCap, eCap⟩ y' := by
  set sp : ℕ → MGraph → MGraph → Embedding → SparsifyOut := fun _ => canonicalSparsify impl
  set info := stepBundleTree sp tr U ord ord'
  set tr' := info.state
  obtain ⟨_, _, _, _, _, hk0, ⟨C_lsst, ℓ₀, hI0, _, _⟩, hP0, hC0, hSB0, hCap0, _, _, _, hLazy0,
    hspV_le0, hspE_le0, hkB0, _, hInact0, hCross0, hInactDyn0, hPart0, hDynG0,
    hLg0, hmMax, hspV_ge, hspE_ge⟩ := hSide
  have hSP : asmBrSP impl w depth y' = asmBrSP impl w depth y := by
    simp only [asmBrSP, hmMax_eq, hspV_eq, hspE_eq, hsplitB]
  have hInactDyn' := asmFirstInactiveDynInv_step sp hSP hI0 hU hOB hk0 hInact0 hCross0 hInactDyn0
  have hPart' := asmFirstActiveBunPartInv_step sp hI0 hU hOB hk0 hInact0 hPart0
  have hDynG' := asmFirstActiveDynGraphInv_step sp hI0 hU hOB hk0 hInact0 hInactDyn0 hPart0 hDynG0
  have hCross' := asmFirstCrossInactiveInv_step (ord := ord) (ord' := ord') sp hI0 hU hCross0
  have hInact' := asmFirstInactiveCompInv_step sp hSP hI0 hU hOB hk0 hInact0 hCross0
  have hBunSubInit : ∀ q ∈ activePairs tr', (tr'.bun q).edges.card ≤ (tr'.initBunG q).m := by
    intro q hq
    obtain ⟨hs, d, _, hst, hG0, hds, hbv, _⟩ := hSpan' q hq
    have hqC := (mem_activePairs.mp hq).1
    have hqb := (mem_activePairs.mp hq).2
    have hEeq := asmFirstActiveDynGraphInv_E hDynG' hqC hqb
    have hVG₀ := (hBUB'.2 q.1 (hF'.2.2.1.1 hqC) q.2).1
    have hGm₀ : d.G₀.m ≤ y'.mMax := by
      rw [hG0, hmMax_eq, hmMax]; exact (hBUB'.2 q.1 (hF'.2.2.1.1 hqC) q.2).2.1
    have hq1 : 1 ≤ d.q (asmBrSP impl w depth y') := le_trans (by decide) (two_le_phaseBase _ _)
    have hInv := (runInv_all (hG0 ▸ hVG₀) hL hq1 hGm₀
      (canonicalSparsify_spec_absorb impl y'.mMax) hbv hds d.flat.length le_rfl).1.G_eq
    have hGeq : (tr'.dyn q).G = d.G₀.applyBatch d.flat := by
      rw [← hst]
      change (runState (L := depth) d.G₀ (d.q (asmBrSP impl w depth y')) (canonicalSparsify impl)
        d.flat d.flat.length).G = _
      simpa [List.take_length] using hInv
    rw [← hEeq, hGeq, ← hG0]
    exact Finset.card_le_card (applyBatch_E_subset_of_delOrSplit _ _ hds)
  have hSpanOK' := restartSlotGraph_spanGraphOK_step hF' hMap' hMatch' hPart'
    (fun C hC b => (hBUB'.2 C hC b).2.1) hBunSubInit
    (by rw [hmMax_eq, hmMax]; rfl) (by rw [hspV_eq, hsplitB]; exact hspV_ge)
    (by rw [hspE_eq]; exact hspE_ge) hL hp hw16 (by rw [hspV_eq, hspE_eq]; exact hw)
    (by rw [hspV_eq, hspE_eq]; exact hcw)
  refine ⟨hMap', hMatch', hSpan', hF'.2.2.1, hSpanOK', hF'.1, hF'.2.1,
    by rw [hmMax_eq]; exact hP0, hC0, by rw [hsplitB]; exact hSB0,
    by rw [hspV_eq, hspE_eq]; exact hCap0, hF'.2.2.2.1, hBunInv', hWP', ?_,
    by rw [hspV_eq, hsplitB]; exact hspV_le0, by rw [hspE_eq]; exact hspE_le0,
    by rw [hkB]; exact hkB0, hSlotInv', hInact', hCross', hInactDyn', hPart', hDynG',
    by rw [hlgFac_eq]; exact hLg0, by rw [hmMax_eq]; exact hmMax,
    by rw [hspV_eq, hsplitB]; exact hspV_ge, by rw [hspE_eq]; exact hspE_ge⟩
  intro C hnotA'
  exact hLazy0 C (fun h => hnotA' (Finset.mem_union_left _ h))

end

end MinCostFlow.SparseCore.Program
