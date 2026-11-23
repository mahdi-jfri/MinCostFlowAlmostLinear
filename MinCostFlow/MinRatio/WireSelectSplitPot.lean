module

public import MinCostFlow.MinRatio.WireSelectUpdateLevel
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Key invariance across vertex splits (`WireSelectSplitPot`)

The coverage theorem of the select heap, `touched_covers_level_changes` (`WireSelectUpdate.lean`),
asks that a surviving edge keep its two ends at every level up to the level of the key
(`hEnds`), and that one family `φ` of frozen potentials serve the chain before and after the
step. Neither holds at an `Update` that deletes a forest edge. When the active forest `F_j`
loses an edge, a tree of `F_j` splits, a new root `v'` appears, and every edge of the core graph
`𝒞(G_j, F_j)` with an end in the split-off part moves its end from the old root `v` to `v'`
(`coreGraph` maps ends to `L.F.root`). So `G_{j+1}` gets a vertex split, and `hEnds` fails at
level `j + 1`.

The keys of such edges do not change, as long as the frozen potential of the new vertex is the
potential of the vertex it split from. The proof of the coverage theorem uses `hEnds` only to show
that `potGrad` is the same before and after the step, and `potGrad` reads the ends only through
`φ`. So this file replaces `hEnds` and the single `φ` by two families `φ` (before) and `φ'`
(after) that agree at the ends of every surviving edge (`EndPotAgree`). At an `Update`, `φ'` is
`φ` with `φ'_j v' = φ_j v` written at each split `v ↦ v'` that enters a level `j` that is not
rebuilt.

* `EndPotAgree C C' φ φ' i`: at every level `j ≤ i`, a surviving edge has the same potential at
  its tail and at its head, read in `φ` before and in `φ'` after.
* `endPotAgree_of_ends`: the old hypotheses (`hEnds`, one `φ`) give `EndPotAgree`.
* `endPotAgree_of_split`: ends that are unchanged, or that moved to a vertex whose new potential
  is the old potential of the old end, give `EndPotAgree`, if `φ'` agrees with `φ` on the old
  vertices.
* `walkInner_and_wlenAt_eq_of_unchanged_emb_phi`, `touched_covers_level_changes_phi`,
  `selectUpdateLevel_establishes_levelOk_phi`: the three select lemmas with `EndPotAgree` in place
  of `hEnds` and the single `φ`.
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open WordRAM MinCostFlow.Num MinCostFlow.Chain DynSpanner.Program

/-- The frozen potentials agree at the ends of every surviving edge: at each level `j ≤ i`, an
edge `f` of both `C.G j` and `C'.G j` has `φ' j` at its new tail equal to `φ j` at its old tail,
and likewise at its head. -/
def EndPotAgree (C C' : TreeChain) (φ φ' : ℕ → ℕ → ℝ) (i : ℕ) : Prop :=
  ∀ j ≤ i, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E →
    φ' j ((C'.G j).tail f) = φ j ((C.G j).tail f) ∧
    φ' j ((C'.G j).head f) = φ j ((C.G j).head f)

/-- If surviving edges keep their ends (`hEnds`), one family `φ` agrees with itself at the ends. -/
theorem endPotAgree_of_ends {C C' : TreeChain} {φ : ℕ → ℕ → ℝ} {i : ℕ}
    (hEnds : ∀ j ≤ i, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E →
      (C'.G j).tail f = (C.G j).tail f ∧ (C'.G j).head f = (C.G j).head f) :
    EndPotAgree C C' φ φ i := fun j hj f hf' hf => by
  rw [(hEnds j hj f hf' hf).1, (hEnds j hj f hf' hf).2]
  exact ⟨rfl, rfl⟩

/-- **Ends across a vertex split.** Let `φ'` agree with `φ` on the old vertices of every level
`j ≤ i`. Let each end of a surviving edge either stay, or move to a vertex whose new potential is
the old potential of the old end (a split `v ↦ v'` with `φ'_j v' = φ_j v`). Then `EndPotAgree`
holds. The old ends are vertices of the old graph by its validity (`hValid`). -/
theorem endPotAgree_of_split {C C' : TreeChain} {φ φ' : ℕ → ℕ → ℝ} {i : ℕ}
    (hValid : ∀ j ≤ i, (C.G j).IsValid)
    (hOld : ∀ j ≤ i, ∀ v ∈ (C.G j).V, φ' j v = φ j v)
    (hTail : ∀ j ≤ i, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E →
      (C'.G j).tail f = (C.G j).tail f ∨ φ' j ((C'.G j).tail f) = φ j ((C.G j).tail f))
    (hHead : ∀ j ≤ i, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E →
      (C'.G j).head f = (C.G j).head f ∨ φ' j ((C'.G j).head f) = φ j ((C.G j).head f)) :
    EndPotAgree C C' φ φ' i := by
  intro j hj f hf' hf
  have hv := hValid j hj f hf
  refine ⟨?_, ?_⟩
  · rcases hTail j hj f hf' hf with h | h
    · rw [h]; exact hOld j hj _ hv.1
    · exact h
  · rcases hHead j hj f hf' hf with h | h
    · rw [h]; exact hOld j hj _ hv.2
    · exact h

/-- `potGrad` at level `i + 1` is the same before and after the step on a surviving edge of level
`i`, if `g` is the same on it and the potentials agree at its ends (`EndPotAgree`). -/
theorem potGrad_eq_of_endPotAgree {C C' : TreeChain} {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    {i : ℕ} (hi : i ≤ C.d) (hi' : i ≤ C'.d) {φ φ' : ℕ → ℕ → ℝ}
    (hEP : EndPotAgree C C' φ φ' i)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    {f : ℕ} (hfGi' : f ∈ (C'.G i).E) (hfGi : f ∈ (C.G i).E) :
    potGrad C' g' φ' (i + 1) f = potGrad C g φ (i + 1) f := by
  rw [potGrad_eq_sum, potGrad_eq_sum]
  have hf0' : f ∈ (C'.G 0).E := C'.G_E_subset_of_le hH' (Nat.zero_le i) hi' hfGi'
  have hf0 : f ∈ (C.G 0).E := C.G_E_subset_of_le hH (Nat.zero_le i) hi hfGi
  rw [hgEq f hf0' hf0]
  congr 1
  refine Finset.sum_congr rfl fun j hj => ?_
  have hji : j ≤ i := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hfj' : f ∈ (C'.G j).E := C'.G_E_subset_of_le hH' hji hi' hfGi'
  have hfj : f ∈ (C.G j).E := C.G_E_subset_of_le hH hji hi hfGi
  rw [(hEP j hji f hfj' hfj).1, (hEP j hji f hfj' hfj).2]

/-- **Signed numerator and denominator invariance, with two potential families.** As
`walkInner_and_wlenAt_eq_of_unchanged_emb` (`WireSelectKeyMath.lean`), with `φ` frozen for `C`,
`φ'` frozen for `C'`, and `EndPotAgree C C' φ φ' i` in place of unchanged ends. -/
theorem walkInner_and_wlenAt_eq_of_unchanged_emb_phi (C C' : TreeChain)
    {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c) (hSpan' : C'.LastLevelSpans)
    {i e : ℕ} (hi : i ≤ C.d) (hi' : i ≤ C'.d)
    (φ φ' : ℕ → ℕ → ℝ)
    (hPot : ∀ j ≤ i, ∀ a b, (C.activeLSF j).F.F.Connected a b →
      walkInner (potGrad C g φ j) ((C.activeLSF j).F.F.forestPath a b) = φ j a - φ j b)
    (hPot' : ∀ j ≤ i, ∀ a b, (C'.activeLSF j).F.F.Connected a b →
      walkInner (potGrad C' g' φ' j) ((C'.activeLSF j).F.F.forestPath a b) = φ' j a - φ' j b)
    (hEP : EndPotAgree C C' φ φ' i)
    (hWstr : ∀ j ≤ i, ∀ f ∈ walkEdges (C.sparsifierCycle i e),
      (C'.activeLSF j).wstr f = (C.activeLSF j).wstr f)
    (hℓEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → ℓ' f = ℓ f)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    (he : e ∈ (C.activeCore i).E \ (C.activeS i).E)
    (he' : e ∈ (C'.activeCore i).E \ (C'.activeS i).E)
    (hEmb : C'.activeEmb i e = C.activeEmb i e) :
    walkInner (C'.chainGrad g' (i + 1)) (C'.sparsifierCycle i e) =
      walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) ∧
    C'.wlenAt ℓ' i e = C.wlenAt ℓ i e := by
  -- The denominator does not read the potentials. The numerator reads them only through
  -- `potGrad` on the edges of the cycle (`potGrad_eq_of_endPotAgree`).
  have hSpEq : C'.sparsifierCycle i e = C.sparsifierCycle i e := by
    unfold TreeChain.sparsifierCycle; rw [hEmb]
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
  have hClosed' := C'.sparsifierCycle_isClosedWalk hH' hSpan' hi' he'
  have hChainLenEq : ∀ k ≤ i + 1, ∀ f ∈ walkEdges (C.sparsifierCycle i e),
      (k = 0 → f ∈ (C'.G 0).E → f ∈ (C.G 0).E → C'.chainLen ℓ' 0 f = C.chainLen ℓ 0 f) ∧
      (∀ m, k = m + 1 → f ∈ (C'.G m).E → f ∈ (C.G m).E →
        C'.chainLen ℓ' (m + 1) f = C.chainLen ℓ (m + 1) f) := by
    intro k
    induction k with
    | zero =>
      intro _ f _
      exact ⟨fun _ hf' hf => hℓEq f hf' hf, fun _ h => by omega⟩
    | succ m ih =>
      intro hm f hfW
      refine ⟨fun h => by omega, fun m' hm' hf' hf => ?_⟩
      have heqm : m' = m := by omega
      subst m'
      have hm_i : m ≤ i := Nat.le_of_succ_le_succ hm
      have hm_d : m ≤ C.d := le_trans hm_i hi
      have hm_d' : m ≤ C'.d := le_trans hm_i hi'
      have hprev : C'.chainLen ℓ' m f = C.chainLen ℓ m f := by
        cases m with
        | zero => exact (ih (Nat.le_of_lt hm) f hfW).1 rfl hf' hf
        | succ m'' =>
          have hf1' : f ∈ (C'.G m'').E :=
            (Finset.mem_sdiff.mp (C'.G_succ_E_subset hH' hm_d' hf')).1
          have hf1 : f ∈ (C.G m'').E := (Finset.mem_sdiff.mp (C.G_succ_E_subset hH hm_d hf)).1
          exact (ih (Nat.le_of_lt hm) f hfW).2 m'' rfl hf1' hf1
      change (C'.activeLSF m).wstr f * C'.chainLen ℓ' m f =
        (C.activeLSF m).wstr f * C.chainLen ℓ m f
      rw [hWstr m hm_i f hfW, hprev]
  have hWlenEq : C'.wlenAt ℓ' i e = C.wlenAt ℓ i e := by
    unfold TreeChain.wlenAt
    rw [hSpEq]
    apply congrArg List.sum
    refine List.map_congr_left fun x hx => ?_
    have hf : x.1 ∈ walkEdges (C.sparsifierCycle i e) := by
      unfold walkEdges; exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨x, hx, rfl⟩)
    have hfCore : x.1 ∈ (C.activeCore i).E := mem_E_of_mem_walkEdges hClosed hf
    have hfCore' : x.1 ∈ (C'.activeCore i).E := mem_E_of_mem_walkEdges hClosed' (hSpEq ▸ hf)
    have hfGi : x.1 ∈ (C.G i).E := (Finset.mem_sdiff.mp hfCore).1
    have hfGi' : x.1 ∈ (C'.G i).E := (Finset.mem_sdiff.mp hfCore').1
    exact (hChainLenEq (i + 1) le_rfl x.1 hf).2 i rfl hfGi' hfGi
  have hGradEq : walkInner (C'.chainGrad g' (i + 1)) (C'.sparsifierCycle i e) =
      walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) := by
    rw [← walkInner_potGrad_eq_chainGrad C' hH' hSpan' φ' hi' hPot' he',
        ← walkInner_potGrad_eq_chainGrad C hH hSpan φ hi hPot he, hSpEq]
    unfold walkInner
    refine Finset.sum_congr rfl fun f hf => ?_
    have hfCore : f ∈ (C.activeCore i).E := mem_E_of_mem_walkEdges hClosed hf
    have hfCore' : f ∈ (C'.activeCore i).E := mem_E_of_mem_walkEdges hClosed' (hSpEq ▸ hf)
    rw [potGrad_eq_of_endPotAgree hH hH' hi hi' hEP hgEq (Finset.mem_sdiff.mp hfCore').1
      (Finset.mem_sdiff.mp hfCore).1]
  exact ⟨hGradEq, hWlenEq⟩

/-- **Coverage across a step with vertex splits.** As `touched_covers_level_changes`
(`WireSelectUpdate.lean`), with `φ` frozen for `C`, `φ'` frozen for `C'`, and
`EndPotAgree C C' φ φ' i` in place of `hEnds`. -/
theorem touched_covers_level_changes_phi
    {C C' : TreeChain} {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hSpan : C.LastLevelSpans) (hSpan' : C'.LastLevelSpans)
    {i : ℕ} (hi : i ≤ C.d) (hi' : i ≤ C'.d)
    (φ φ' : ℕ → ℕ → ℝ)
    (hPot : SelectPotInv C g φ) (hPot' : SelectPotInv C' g' φ')
    (hEP : EndPotAgree C C' φ φ' i)
    {ins : ℕ → ℕ → Prop}
    (hWstr : ∀ j ≤ i, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E → ¬ ins j f →
      (C'.activeLSF j).wstr f = (C.activeLSF j).wstr f)
    (hInsFwd : ∀ j < i, ∀ f ∈ (C'.G (j + 1)).E, f ∈ (C.G (j + 1)).E → ins j f → ins (j + 1) f)
    (hℓEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → ℓ' f = ℓ f)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    {lists : LevelDiffLists} (hcov : LevelDiffCovers C C' i ins lists)
    {e : ℕ} (hnotTouched : e ∉ lists.allTouched) :
    (e ∈ (C'.activeCore i).E \ (C'.activeS i).E ↔
      e ∈ (C.activeCore i).E \ (C.activeS i).E) ∧
    (e ∈ (C'.activeCore i).E \ (C'.activeS i).E →
      walkInner (C'.chainGrad g' (i + 1)) (C'.sparsifierCycle i e) =
        walkInner (C.chainGrad g (i + 1)) (C.sparsifierCycle i e) ∧
      C'.wlenAt ℓ' i e = C.wlenAt ℓ i e) := by
  obtain ⟨huG, hfDel, hfIns, huS, hreemb, hreembIns⟩ := hcov
  have hnotUG : e ∉ lists.uG := fun h => hnotTouched (by simp [LevelDiffLists.allTouched, h])
  have hnotFD : e ∉ lists.fDel := fun h => hnotTouched (by simp [LevelDiffLists.allTouched, h])
  have hnotUS : e ∉ lists.uS := fun h => hnotTouched (by simp [LevelDiffLists.allTouched, h])
  have hnotRe : e ∉ lists.reemb := fun h => hnotTouched (by simp [LevelDiffLists.allTouched, h])
  have hGiff : e ∈ (C'.G i).E ↔ e ∈ (C.G i).E := by
    by_contra hne
    have hxor : e ∈ (C'.G i).E ↔ e ∉ (C.G i).E := by tauto
    exact hnotUG (huG e (Or.inl hxor))
  have hFiff : e ∈ (C'.activeLSF i).F.F.E ↔ e ∈ (C.activeLSF i).F.F.E := by
    constructor
    · intro h'; by_contra h; exact hnotUG (hfIns e h' h)
    · intro h; by_contra h'; exact hnotFD (hfDel e h h')
  have hSiff : e ∈ (C'.activeS i).E ↔ e ∈ (C.activeS i).E := by
    by_contra hne
    have hxor : e ∈ (C'.activeS i).E ↔ e ∉ (C.activeS i).E := by tauto
    exact hnotUS (huS e hxor)
  have hCandIff : e ∈ (C'.activeCore i).E \ (C'.activeS i).E ↔
      e ∈ (C.activeCore i).E \ (C.activeS i).E := by
    simp only [TreeChain.activeCore, coreGraph, Finset.mem_sdiff, hGiff, hFiff, hSiff]
  refine ⟨hCandIff, fun he' => ?_⟩
  have he : e ∈ (C.activeCore i).E \ (C.activeS i).E := hCandIff.mp he'
  have hemb : C'.activeEmb i e = C.activeEmb i e := by
    by_contra hne; exact hnotRe (hreemb e he he' hne)
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hi he
  have hClosed' := C'.sparsifierCycle_isClosedWalk hH' hSpan' hi' he'
  have hSpEq : C'.sparsifierCycle i e = C.sparsifierCycle i e := by
    unfold TreeChain.sparsifierCycle; rw [hemb]
  have hNotIns : ∀ j ≤ i, ∀ f ∈ walkEdges (C.sparsifierCycle i e), ¬ ins j f := by
    intro j hj f hfW hInsJ
    have hfGi : f ∈ (C.G i).E := (Finset.mem_sdiff.mp (mem_E_of_mem_walkEdges hClosed hfW)).1
    have hfGi' : f ∈ (C'.G i).E :=
      (Finset.mem_sdiff.mp (mem_E_of_mem_walkEdges hClosed' (hSpEq ▸ hfW))).1
    have hProp : ∀ k, j ≤ k → k ≤ i → ins k f := by
      intro k hjk
      induction k with
      | zero =>
        intro _
        have : j = 0 := by omega
        subst this; exact hInsJ
      | succ k ih =>
        intro hki
        by_cases hjeq : j = k + 1
        · subst hjeq; exact hInsJ
        · exact hInsFwd k (by omega) f (C'.G_E_subset_of_le hH' hki hi' hfGi')
            (C.G_E_subset_of_le hH hki hi hfGi) (ih (by omega) (by omega))
    have hInsI : ins i f := hProp i hj le_rfl
    obtain ⟨dir, hmem⟩ := LSF.mem_walkEdges_iff.mp hfW
    unfold TreeChain.sparsifierCycle at hmem
    rcases List.mem_cons.mp hmem with heq | hrev
    · have hfe : f = e := congrArg Prod.fst heq
      exact hnotUG (huG e (Or.inr (hfe ▸ hInsI)))
    · obtain ⟨y, hy, hyEq⟩ := List.mem_map.mp (List.mem_reverse.mp hrev)
      have hfy : y.1 = f := congrArg Prod.fst hyEq
      exact hnotRe (hreembIns e he he' ⟨y, hy, hfy ▸ hInsI⟩)
  exact walkInner_and_wlenAt_eq_of_unchanged_emb_phi C C' hH hSpan hH' hSpan' hi hi' φ φ'
    (fun j hj => hPot j (le_trans hj hi)) (fun j hj => hPot' j (le_trans hj hi'))
    hEP (fun j hj f hfW =>
      have hfGi : f ∈ (C.G i).E := (Finset.mem_sdiff.mp (mem_E_of_mem_walkEdges hClosed hfW)).1
      have hfGi' : f ∈ (C'.G i).E :=
        (Finset.mem_sdiff.mp (mem_E_of_mem_walkEdges hClosed' (hSpEq ▸ hfW))).1
      hWstr j hj f (C'.G_E_subset_of_le hH' hj hi' hfGi') (C.G_E_subset_of_le hH hj hi hfGi)
        (hNotIns j hj f hfW))
    hℓEq hgEq he he' hemb

/-- **`selectUpdateLevel` across a step with vertex splits.** As
`selectUpdateLevel_establishes_levelOk` (`WireSelectUpdateLevel.lean`), with `φ` frozen for `C`,
`φ'` frozen for `C'` (the potentials of the metadata after the step), and
`EndPotAgree C C' φ φ' lvl` in place of `hEnds`. -/
theorem selectUpdateLevel_establishes_levelOk_phi
    {w h P : ℕ} {loc : SelectHeapLoc} {mloc : SelectLevelMetaLoc}
    {C C' : TreeChain} {G G' : MGraph} {ℓ ℓ' g g' : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c σ' σ'_mwu γ'_ℓ γ'_c : ℝ}
    {φ φ' coreLen : ℕ → ℕ → ℝ} {L : LevelDiffLists}
    {evalSpace evalCost lvl diffBase scratch ret : ℕ} {mem mem' : ℕ → ℕ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hH' : C'.Holds G' ℓ' σ' σ'_mwu γ'_ℓ γ'_c)
    (hSpan : C.LastLevelSpans) (hSpan' : C'.LastLevelSpans)
    (hlvl : lvl ≤ C.d) (hlvl' : lvl ≤ C'.d)
    (hPot : SelectPotInv C g φ) (hPot' : SelectPotInv C' g' φ')
    (hEP : EndPotAgree C C' φ φ' lvl)
    {ins : ℕ → ℕ → Prop}
    (hWstr : ∀ j ≤ lvl, ∀ f ∈ (C'.G j).E, f ∈ (C.G j).E → ¬ ins j f →
      (C'.activeLSF j).wstr f = (C.activeLSF j).wstr f)
    (hInsFwd : ∀ j < lvl, ∀ f ∈ (C'.G (j + 1)).E, f ∈ (C.G (j + 1)).E → ins j f → ins (j + 1) f)
    (hℓEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → ℓ' f = ℓ f)
    (hgEq : ∀ f ∈ (C'.G 0).E, f ∈ (C.G 0).E → g' f = g f)
    (hcov : LevelDiffCovers C C' lvl ins L)
    (hLbd : ∀ e ∈ L.allTouched, e < loc.cap)
    (hOldOk : SelectHeapLevelOk mem loc h P C g ℓ lvl)
    (hPost : (selectUpdateLevelContract w h P loc mloc C' g' ℓ' φ' coreLen L evalSpace evalCost).post
      [loc.hb, mloc.metaBase, lvl, diffBase, scratch] mem ret mem') :
    SelectHeapLevelOk mem' loc h P C' g' ℓ' lvl ∧
    (∀ e' < loc.cap, e' ∉ (C'.activeCore lvl).E \ (C'.activeS lvl).E →
      (mem (loc.posPtr + e') = 0 → mem' (loc.posPtr + e') = 0) ∧
      (mem (loc.posPtr + e') ≠ 0 → mem (loc.lvlPtr + e') ≠ lvl →
        mem' (loc.posPtr + e') ≠ 0 ∧ mem' (loc.lvlPtr + e') = mem (loc.lvlPtr + e') ∧
        loc.readNum mem' h e' = loc.readNum mem h e' ∧
        loc.readDen mem' h e' = loc.readDen mem h e')) := by
  obtain ⟨_, _, _, _, _, hin, hout⟩ := hPost
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hin hout
  have hCovAt := fun e (hT : e ∉ L.allTouched) =>
    touched_covers_level_changes_phi hH hH' hSpan hSpan' hlvl hlvl' φ φ' hPot hPot' hEP hWstr
      hInsFwd hℓEq hgEq hcov hT
  refine ⟨⟨fun e heCap hnz hl => ?_, fun e he => ?_⟩, fun e' he' hnc => ?_⟩
  · by_cases hT : e ∈ L.allTouched
    · by_contra hnc; exact ((hin e hT).2 hnc).1 ⟨hnz, hl⟩
    · obtain ⟨k1, k2, _, _⟩ := hout e heCap hT
      have hOld : e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E :=
        hOldOk.1 e heCap (k1.mp hnz) (k2.symm.trans hl)
      exact (hCovAt e hT).1.mpr hOld
  · by_cases hT : e ∈ L.allTouched
    · exact ⟨hLbd e hT, (hin e hT).1 he⟩
    · have hCov := hCovAt e hT
      have hOld : e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E := hCov.1.mp he
      obtain ⟨heCap, hnz0, hl0, hrep0⟩ := hOldOk.2 e hOld
      obtain ⟨k1, k2, k3, k4⟩ := hout e heCap hT
      obtain ⟨hwi, hwl⟩ := hCov.2 he
      exact ⟨heCap, k1.mpr hnz0, k2.trans hl0, by rw [k3, k4, hwi, hwl]; exact hrep0⟩
  · by_cases hT : e' ∈ L.allTouched
    · exact ⟨((hin e' hT).2 hnc).2.1, ((hin e' hT).2 hnc).2.2.1⟩
    · obtain ⟨k1, k2, k3, k4⟩ := hout e' he' hT
      exact ⟨fun h0 => by by_contra hnz; exact (k1.mp hnz) h0,
        fun hnz _ => ⟨k1.mpr hnz, k2, k3, k4⟩⟩

end MinCostFlow.MinRatio
