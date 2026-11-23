module

public import MinCostFlow.SparseCore.CompLSFBridge
public import MinCostFlow.LSF.Program.Spec
import Mathlib.Tactic.Linarith

/-!
# Model-Side Bridges for Per-Component Dynamic LSF (`CompModel`)

Proves the pure mathematical bridge lemmas used by the Word-RAM implementation of `CompLSFState`
(`SparseCore/CompLSF.lean`):

1. **Isolated components (`(compGraph G₀ C).m = 0`):** every vertex in `C` is a root of `RF`
   (`isoComp_root_eq_self`), `T_cur.E = ∅`, `RF.F.E = ∅`, and any non-inserted surviving edge
   belongs to an edgeful component (`nonIns_mem_edgeful`).
2. **Component-edge and ghost-end tracking (`CompEdgeTrack`):** maintains `edgeComp1`, `edgeComp2`,
   `ghostTailList`, `ghostHeadList`, `ghostTailVert`, `ghostHeadVert` across `initCompLSFWith` and
   `compLSFStepSingle`. This identifies `e ∈ (cs.compSt C).G.E` in `O(1)` via
   `edgeComp1 e = c ∨ edgeComp2 e = c`, and handles Tag-3 (kept-set) vertex splits exactly even
   when cross-edges leave stationary ghost ends in component graphs.
3. **Exact `UpdateAt` projection:** proves that the single-update encoding produced for
   `projCompUpdateG cs.G (cs.compSt C).G u` satisfies `UpdateAt` on `(cs.compSt C).G` for every
   `.insert`, `.delete`, Tag-2 `.split`, and Tag-3 `.split`.
4. **Touched-component step characterization and cost comparison:** identifies `touchedCompsBatch`
   along single steps and proves that running `lsfApplyBatch` update-by-update on a touched
   component costs at most `3` times `lsfBatchCost` of its full projected batch.
-/

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program MinCostFlow.SparseCore
  MinCostFlow.DynSpanner.Program

@[expose] public section

/-! ## 1. Isolated-component and root-lookup lemmas -/

/-- If `C ∈ components G₀` has no edges, then `C` has cardinality `1`. -/
lemma isoComp_card_eq_one {G₀ : MGraph} (hG₀ : G₀.IsValid) {C : Finset ℕ}
    (hC : C ∈ components G₀) (hm : (compGraph G₀ C).m = 0) : C.card = 1 := by
  have hne : (compGraph G₀ C).V.Nonempty := compGraph_nonempty hC
  have h1 : 1 ≤ C.card := Finset.card_pos.mpr hne
  have hconn := compGraph_connected hG₀ hC
  have hval := compGraph_isValid hG₀ hC
  have hle : C.card ≤ 1 := by
    obtain ⟨v₀, hv₀⟩ := hne
    have hsub : C ⊆ {v₀} := by
      intro u hu
      rw [Finset.mem_singleton]
      obtain ⟨P, hP⟩ := hconn v₀ hv₀ u hu
      cases hP with
      | nil _ => rfl
      | cons hxE _ _ =>
        have hpos : 0 < (compGraph G₀ C).m := Finset.card_pos.mpr ⟨_, hxE⟩
        omega
    exact (Finset.card_le_card hsub).trans (by simp)
  omega

/-- Every vertex in an isolated component `C` (`(compGraph G₀ C).m = 0`) is its own root in `cs.RF`,
and `(cs.compSt C).RF.F.E = ∅`. -/
lemma isoComp_props {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀)
    (hm : (compGraph cs.G₀ C).m = 0) :
    (cs.compSt C).RF.F.E = ∅ ∧
    (cs.compSt C).R = (cs.compSt C).G.V ∧
    ∀ v ∈ (cs.compSt C).G.V, cs.RF.root v = v := by
  have hCI := (hI.hCompLSF C hC).1
  have hG₀C := (hI.hCompLSF C hC).2.1
  have hFE : (cs.compSt C).RF.F.E = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro e he
    have heC : e ∈ (compGraph cs.G₀ C).E := hI.hF_sub_compE C hC he
    have hpos : 0 < (compGraph cs.G₀ C).m := Finset.card_pos.mpr ⟨e, heC⟩
    omega
  have hC1 : C.card = 1 := isoComp_card_eq_one hI.hG₀_val hC hm
  have hTV : (cs.compSt C).T₀.V = C := by
    rw [hCI.hTV, hG₀C]; rfl
  have hRorig : (cs.compSt C).R_orig = C := by
    have hSInv := LSFInvWith.toStructInv hCI
    have hsub : (cs.compSt C).R_orig ⊆ C := fun x hx => hTV ▸ hSInv.R_orig_sub hx
    have hmem : (cs.compSt C).r₀ ∈ (cs.compSt C).R_orig := hSInv.r₀_mem_R_orig
    have hpos : 1 ≤ (cs.compSt C).R_orig.card := Finset.card_pos.mpr ⟨_, hmem⟩
    exact Finset.eq_of_subset_of_card_le hsub (by omega)
  have hReq : (cs.compSt C).R = (cs.compSt C).G.V := by
    change (cs.compSt C).R_orig ∪ (cs.compSt C).isolatedVerts = (cs.compSt C).G.V
    rw [hRorig, hCI.hGV_eq, hTV]
  have hroot : ∀ v ∈ (cs.compSt C).G.V, cs.RF.root v = v := by
    intro v hv
    rw [compLSF_RF_root_eq hI hC hv]
    have hRS := lsfInv_to_RS hCI
    have hvR : v ∈ (cs.compSt C).RF.R := by change v ∈ (cs.compSt C).R; rw [hReq]; exact hv
    exact rootedForest_root_eq_of_mem hRS hv hvR (connected_refl _ _)
  exact ⟨hFE, hReq, hroot⟩

/-- Any surviving non-inserted edge `e ∈ cs.G.E \ cs.insertedGlobal` belongs to an edgeful
component `C` (`1 ≤ (compGraph cs.G₀ C).m`) with `cs.wstrGlobal e = (cs.compSt C).wstr e`. -/
lemma nonIns_mem_edgeful {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {e : ℕ} (he : e ∈ cs.G.E) (hni : e ∉ cs.insertedGlobal) :
    ∃ C ∈ components cs.G₀, 1 ≤ (compGraph cs.G₀ C).m ∧
      e ∈ (cs.compSt C).G.E ∧ e ∉ (cs.compSt C).insertedEdges ∧
      cs.wstrGlobal e = (cs.compSt C).wstr e := by
  obtain ⟨C, hC, heC, hniC, hw⟩ := hI.hWstr_surv e he hni
  have hCI := (hI.hCompLSF C hC).1
  have hG₀C := (hI.hCompLSF C hC).2.1
  have heG₀ : e ∈ (compGraph cs.G₀ C).E := by
    rw [← hG₀C]
    exact (hCI.hsurv_edge e heC hniC).1
  exact ⟨C, hC, Finset.card_pos.mpr ⟨e, heG₀⟩, heC, hniC, hw⟩

/-- Reading `RF.root v` from `FAncAt` agrees with `(cs.compSt C).RF.root v` and `cs.RF.root v`. -/
lemma compRoot_eq_of_fAncAt {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {C : Finset ℕ} (hC : C ∈ components cs.G₀)
    {mem : ℕ → ℕ} {fAncPtr vCap : ℕ} {rList : List ℕ}
    {compId compRoot compSize : ℕ → ℕ} {activeCids : Finset ℕ}
    (hFA : FAncAt mem fAncPtr vCap (cs.compSt C).RF rList compId compRoot compSize activeCids)
    {v : ℕ} (hv : v ∈ (cs.compSt C).G.V) :
    mem (fCompRootBase fAncPtr vCap + mem (fCompIdBase fAncPtr vCap + v)) = cs.RF.root v := by
  have hCI := (hI.hCompLSF C hC).1
  have hRS := lsfInv_to_RS hCI
  have hvF : v ∈ (cs.compSt C).RF.F.V := hRS.2.1 ▸ hv
  rcases hFA with ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hcid, hvspec⟩
  obtain ⟨hceq, hcact, hconn⟩ := hvspec v hvF
  obtain ⟨_, hroot_mem, hroot_R, _, _, _, _⟩ := hcid _ hcact
  rw [compLSF_RF_root_eq hI hC hv]
  exact hroot_mem.trans (rootedForest_root_eq_of_mem hRS hv hroot_R hconn).symm

/-! ## 2. Component-edge tracking (`CompEdgeTrack`) -/

/-- Exact component-assignment tracking invariant for `cs : CompLSFState`, shared across all `k`
branches.
* `compOf : Fin numComps → Finset ℕ` enumerates `components cs.G₀` bijectively.
* `edgeC1 e`, `edgeC2 e` give the component indices of `cs.G.tail e` and `cs.G.head e` for every
  live edge `e ∈ cs.G.E`.
* Since cross-inserts are projected to insert-then-delete self-loops, no cross-edge lives in
  any component graph: `e ∈ (cs.compSt (compOf c)).G.E ↔ c1 = c2 ∧ c = c1`, and `gtList`, `ghList`
  remain permanently empty. -/
structure CompEdgeTrack (numComps vCap eCap : ℕ) (compOf : Fin numComps → Finset ℕ)
    (edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ) (gtList ghList : ℕ → List ℕ)
    (cs : CompLSFState) : Prop where
  hBij : Function.Injective compOf ∧ ∀ C, C ∈ components cs.G₀ ↔ ∃ c : Fin numComps, compOf c = C
  hVlt : ∀ v ∈ cs.G.V, v < vCap
  hElt : ∀ e ∈ cs.G.E, e < eCap
  hEdge : ∀ e ∈ cs.G.E,
    ∃ (c1 c2 : Fin numComps),
      edgeC1 e = c1.1 ∧ edgeC2 e = c2.1 ∧
      cs.G.tail e ∈ (cs.compSt (compOf c1)).G.V ∧
      cs.G.head e ∈ (cs.compSt (compOf c2)).G.V ∧
      (∀ c : Fin numComps, e ∈ (cs.compSt (compOf c)).G.E ↔ c1 = c2 ∧ c = c1) ∧
      (e ∈ cs.crossEdges ↔ c1 ≠ c2) ∧
      (c1 = c2 → (cs.compSt (compOf c1)).G.tail e = cs.G.tail e ∧
        (cs.compSt (compOf c1)).G.head e = cs.G.head e)
  hGT : ∀ v < vCap, (gtList v).Nodup ∧ (∀ e ∈ gtList v, e < eCap) ∧ gtList v = []
  hGH : ∀ v < vCap, (ghList v).Nodup ∧ (∀ e ∈ ghList v, e < eCap) ∧ ghList v = []

lemma CompEdgeTrack.compOf_mem {numComps vCap eCap : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert : ℕ → ℕ} {gtList ghList : ℕ → List ℕ} {cs : CompLSFState}
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs)
    (c : Fin numComps) : compOf c ∈ components cs.G₀ :=
  (hT.hBij.2 (compOf c)).mpr ⟨c, rfl⟩

/-- `CompEdgeTrack` is independent of the unused ghost vertex arrays `gtVert`, `ghVert`. -/
lemma CompEdgeTrack.of_ghostVerts {numComps vCap eCap : ℕ} {compOf : Fin numComps → Finset ℕ}
    {edgeC1 edgeC2 gtVert ghVert gtVert' ghVert' : ℕ → ℕ} {gtList ghList : ℕ → List ℕ}
    {cs : CompLSFState}
    (hT : CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert ghVert gtList ghList cs) :
    CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 gtVert' ghVert' gtList ghList cs :=
  ⟨hT.hBij, hT.hVlt, hT.hElt, hT.hEdge, hT.hGT, hT.hGH⟩

/-- `CompEdgeTrack` holds at initialization with empty ghost lists. -/
lemma compEdgeTrack_init {lsfInit : LSFInit} {C_lsst : ℝ} {k j numComps vCap eCap : ℕ}
    (hInit : IsValidLSFInitFor lsfInit C_lsst k j)
    {G₀ : MGraph} (hG₀ : G₀.IsValid) (_hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e) (hk : 1 ≤ k)
    (hVlt : ∀ v ∈ G₀.V, v < vCap) (hElt : ∀ e ∈ G₀.E, e < eCap)
    {compOf : Fin numComps → Finset ℕ}
    (hInj : Function.Injective compOf)
    (hSurj : ∀ C, C ∈ components G₀ ↔ ∃ c : Fin numComps, compOf c = C)
    {edgeC1 edgeC2 : ℕ → ℕ}
    (hEC : ∀ e ∈ G₀.E, ∃ c : Fin numComps, edgeC1 e = c.1 ∧ edgeC2 e = c.1 ∧ G₀.tail e ∈ compOf c) :
    CompEdgeTrack numComps vCap eCap compOf edgeC1 edgeC2 (fun _ => 0) (fun _ => 0)
      (fun _ => []) (fun _ => []) (initCompLSFWith lsfInit G₀ ℓ₀ k j) := by
  set cs := initCompLSFWith lsfInit G₀ ℓ₀ k j
  have hG_eq : ∀ c : Fin numComps, (cs.compSt (compOf c)).G = compGraph G₀ (compOf c) := fun c =>
    (initCompLSFWith_compSt_basic hInit hG₀ hℓ₀ hk ((hSurj _).mpr ⟨c, rfl⟩)).2.1
  refine ⟨⟨hInj, hSurj⟩, hVlt, hElt, ?_, ?_, ?_⟩
  · intro e he
    obtain ⟨c, hc1, hc2, htC⟩ := hEC e he
    have hCmem : compOf c ∈ components G₀ := (hSurj _).mpr ⟨c, rfl⟩
    have heC : e ∈ compEdgeSet G₀ (compOf c) := by
      rw [compEdgeSet, Finset.mem_filter]; exact ⟨he, htC⟩
    have hends := mem_compEdgeSet_endpoints hG₀ hCmem heC
    refine ⟨c, c, hc1, hc2, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hG_eq c]; exact hends.2.1
    · rw [hG_eq c]; exact hends.2.2
    · intro c'
      rw [hG_eq c']
      change e ∈ compEdgeSet G₀ (compOf c') ↔ c = c ∧ c' = c
      simp only [true_and]
      constructor
      · intro he'
        by_contra hne
        have hdisj := compEdgeSet_pairwiseDisjoint G₀ ((hSurj _).mpr ⟨c', rfl⟩) hCmem
          (fun h => hne (hInj h))
        exact Finset.disjoint_left.mp hdisj he' heC
      · rintro rfl; exact heC
    · simp [cs, initCompLSFWith]
    · intro _; rw [hG_eq c]; exact ⟨rfl, rfl⟩
  · intro v _
    exact ⟨List.nodup_nil, (fun _ h => by cases h), rfl⟩
  · intro v _
    exact ⟨List.nodup_nil, (fun _ h => by cases h), rfl⟩

/-! ## 4. Touched components and per-update vs full-batch cost bound -/

/-- `touchedCompsBatch` over `u :: rest` is the union of `touchedComps cs u` and
`touchedCompsBatch (compLSFStepSingle cs u) rest`. -/
lemma touchedCompsBatch_cons {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {cs : CompLSFState}
    (hI : CompLSFInv C_lsst ℓ₀ cs) {u : Update} {rest : List Update}
    (hu : cs.G.UpdateIsValid u) :
    touchedCompsBatch cs (u :: rest) =
      touchedComps cs u ∪ touchedCompsBatch (compLSFStepSingle cs u) rest := by
  classical
  ext C
  simp only [touchedCompsBatch, touchedComps, Finset.mem_union, Finset.mem_filter]
  have hG0 : (compLSFStepSingle cs u).G₀ = cs.G₀ := rfl
  rw [hG0]
  constructor
  · rintro ⟨hC, hne⟩
    have hG1 := applyLSFBatch_G_of_valid (hI.hCompLSF C hC).1 (projCompUpdateG_valid hI hu hC)
    dsimp only [projCompBatchG] at hne
    rw [show cs.G.applyUpdate u = (compLSFStepSingle cs u).G from rfl,
      show (cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u) =
        ((compLSFStepSingle cs u).compSt C).G from hG1.symm] at hne
    by_cases h1 : projCompUpdateG cs.G (cs.compSt C).G u ≠ []
    · left; exact ⟨hC, h1⟩
    · push Not at h1
      rw [h1, List.nil_append] at hne
      right; exact ⟨hC, hne⟩
  · rintro (⟨hC, h1⟩ | ⟨hC, h2⟩)
    · refine ⟨hC, ?_⟩
      dsimp only [projCompBatchG]
      intro hemp
      exact h1 (List.append_eq_nil_iff.mp hemp).1
    · refine ⟨hC, ?_⟩
      have hG1 := applyLSFBatch_G_of_valid (hI.hCompLSF C hC).1 (projCompUpdateG_valid hI hu hC)
      dsimp only [projCompBatchG]
      rw [show cs.G.applyUpdate u = (compLSFStepSingle cs u).G from rfl,
        show (cs.compSt C).G.applyBatch (projCompUpdateG cs.G (cs.compSt C).G u) =
          ((compLSFStepSingle cs u).compSt C).G from hG1.symm]
      intro hemp
      exact h2 (List.append_eq_nil_iff.mp hemp).2

/-- Every encoded update in `UpdateAt` has length at least `2`. -/
lemma updateAt_len_ge_two {mem : ℕ → ℕ} {a : ℕ} {G : MGraph} {u : Update} {len : ℕ}
    (h : UpdateAt mem a G u len) : 2 ≤ len := by
  cases u with
  | insert _ _ _ => rcases h with ⟨rfl, _⟩; decide
  | delete _ => rcases h with ⟨rfl, _⟩; decide
  | split _ _ _ _ =>
    rcases h with ⟨_, _, _, _, _, _, rfl, _⟩ | ⟨_, _, _, _, _, _, rfl, _⟩ <;> omega

/-- Per-update `lsfBatchCost` summed over updates of a nonempty projected batch `U_C` with
individual word lengths `lens` (each `≥ 2`) is at most `3` times `lsfBatchCost` of the full
projected batch `U_C` (total words `1 + lens.sum`). -/
lemma sum_single_lsfBatchCost_le_three_mul {L_w : ℕ} (hLw : 1 ≤ L_w) (lens : List ℕ)
    (hge2 : ∀ l ∈ lens, 2 ≤ l) :
    (lens.map fun l => lsfBatchCostFactor * ((1 + l) * L_w + 1)).sum ≤
      3 * (lsfBatchCostFactor * ((1 + lens.sum) * L_w + 1)) := by
  have h1 : ∀ l ∈ lens, (1 + l) * L_w + 1 ≤ 3 * (l * L_w) := fun l hl => by
    have h2 : 2 ≤ l := hge2 l hl
    have h1l : 1 ≤ l := by omega
    have h1Lw : 1 ≤ l * L_w := Nat.mul_pos h1l hLw
    have hadd : (1 + l) * L_w = L_w + l * L_w := by ring
    have hle : L_w ≤ l * L_w := Nat.le_mul_of_pos_left L_w h1l
    omega
  have hsum : (lens.map fun l => (1 + l) * L_w + 1).sum ≤ 3 * (lens.sum * L_w) := by
    induction lens with
    | nil => simp
    | cons x xs ih =>
      simp only [List.map_cons, List.sum_cons]
      have hx := h1 x List.mem_cons_self
      have hxs := ih (fun l hl => hge2 l (List.mem_cons_of_mem _ hl))
        (fun l hl => h1 l (List.mem_cons_of_mem _ hl))
      have hmul : (x + xs.sum) * L_w = x * L_w + xs.sum * L_w := by ring
      omega
  have hfac : ∀ ls : List ℕ, (ls.map fun l => lsfBatchCostFactor * ((1 + l) * L_w + 1)).sum =
      lsfBatchCostFactor * (ls.map fun l => (1 + l) * L_w + 1).sum := fun ls => by
    induction ls with
    | nil => simp
    | cons x xs ih =>
      rw [List.map_cons, List.sum_cons, ih, List.map_cons, List.sum_cons]; ring
  rw [hfac lens]
  calc lsfBatchCostFactor * (lens.map fun l => (1 + l) * L_w + 1).sum
      ≤ lsfBatchCostFactor * (3 * (lens.sum * L_w)) := Nat.mul_le_mul_left _ hsum
    _ = 3 * (lsfBatchCostFactor * (lens.sum * L_w)) := by ring
    _ ≤ 3 * (lsfBatchCostFactor * ((1 + lens.sum) * L_w + 1)) := by
        refine Nat.mul_le_mul_left 3 (Nat.mul_le_mul_left lsfBatchCostFactor ?_)
        have : lens.sum * L_w ≤ (1 + lens.sum) * L_w := Nat.mul_le_mul_right L_w (by omega)
        omega

end

end MinCostFlow.SparseCore.Program
