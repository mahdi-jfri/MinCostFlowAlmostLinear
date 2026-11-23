module

public import MinCostFlow.SparseCore.MWU
public import MinCostFlow.SparseCore.GraphHelpers
public import MinCostFlow.Chain.CoreGraph
public import MinCostFlow.Chain.EncodingSize
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Dynamic Core Graph Maintenance (`Lemma 5.14`, `jtree.tex` pp. 22–23)

This file formalizes Lemma 5.14: given a dynamic graph `G` undergoing valid updates `U` and a
dynamic `LSFState` maintained by `applyLSFUpdate`, we maintain the core graph
`C = coreGraph S.G S.lsf` (vertices `S.R`, off-forest edges `S.G.E \ S.RF.F.E`) explicitly via
valid dynamic update batches `coreStepBatch S u` and `coreBatch S U`.

Key proved properties:
* **Euler forest edge-loss bound** (`lsf_forest_diff_le_R_diff`): each single update `u` deletes
  at most `(S'.R \ S.R).card` edges from `S.RF.F.E`.
* **Exact `coreGraph` transition** (`coreStepBatch_spec`, `coreBatch_spec`): `coreBatch S U` is
  `BatchIsValid` and transitions `C` to a graph `GraphEq` to `coreGraph S'.G S'.lsf`.
* **Explicit recourse & encoding bound** (`lemma_5_14`, plus `lemma_2_1` giving `Õ(C₀.m + q_C)`).
* **Exact self-loop splitting** (`coreGraph_split_selfLoop_breaks`): under independent
  `Update.split v v' St Sh`, splitting `(r, r)` self-loops into `(r₁', r₂')` (`r₁' ≠ r₂'`) directly
  updates only the relevant endpoints without deleting and reinserting edges.
-/

@[expose] public section

namespace MinCostFlow.SparseCore

open MinCostFlow MinCostFlow.LSF MinCostFlow.Chain

/-! ## Euler forest edge-loss bound and `LSFInv` projection helpers -/

/-- Exact Euler forest identity for any valid `RootedForest`: `R.card + F.E.card = G.V.card`. -/
lemma rootedForest_R_add_edges {RF : RootedForest} {G : MGraph}
    (hRF : RF.IsRootedSpanningForestOf G) :
    RF.R.card + RF.F.E.card = G.V.card := by
  have hcomp := rootedForest_components_card hRF
  have heuler := forest_components_add_edges RF.F hRF.1
  have hVc : RF.F.V.card = G.V.card := congrArg Finset.card hRF.2.1
  omega

/-- Extract `S.RF.IsRootedSpanningForestOf S.G` unconditionally from `LSFInvWith thresh K_σ ℓ₀ S`. -/
lemma lsfInv_to_RS {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) :
    S.RF.IsRootedSpanningForestOf S.G :=
  hI.to_RF_spanning

/-- `S.R ⊆ S.G.V` from `LSFInvWith`. -/
lemma lsfInv_R_sub_V {thresh K_σ : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState}
    (hI : LSFInvWith thresh K_σ ℓ₀ S) :
    S.R ⊆ S.G.V :=
  (lsfInv_to_RS hI).2.2.1

/-- For a decremental rooted spanning forest step `(S → S')` along `u`,
`|(S.RF.F.E \ S'.RF.F.E)| ≤ (S'.R \ S.R).card` via the Euler forest identity. -/
lemma lsf_forest_diff_le_R_diff {S S' : LSFState} {u : Update}
    (hRF : S.RF.IsRootedSpanningForestOf S.G)
    (hRF' : S'.RF.IsRootedSpanningForestOf S'.G)
    (hG' : S'.G = S.G.applyUpdate u)
    (hu : S.G.UpdateIsValid u)
    (hR_sub : S.R ⊆ S'.R)
    (hFE_sub : S'.RF.F.E ⊆ S.RF.F.E) :
    (S.RF.F.E \ S'.RF.F.E).card ≤ (S'.R \ S.R).card := by
  have he1 := rootedForest_R_add_edges hRF
  have he2 := rootedForest_R_add_edges hRF'
  have hR_le : S.R.card ≤ S'.R.card := Finset.card_le_card hR_sub
  have hF_le : S'.RF.F.E.card ≤ S.RF.F.E.card := Finset.card_le_card hFE_sub
  have hR_diff : (S'.R \ S.R).card = S'.R.card - S.R.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hR_sub]
  have hF_diff : (S.RF.F.E \ S'.RF.F.E).card = S.RF.F.E.card - S'.RF.F.E.card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hFE_sub]
  have hV_le : S.G.V.card ≤ S'.G.V.card := by
    rw [hG']
    cases u with
    | delete _ => exact le_rfl
    | insert _ _ _ => exact le_rfl
    | split _ v' _ _ =>
      dsimp only [MGraph.applyUpdate]
      rw [Finset.card_insert_of_notMem hu.2.1]
      exact Nat.le_succ _
  have hSR : S.RF.R = S.R := rfl
  have hS'R : S'.RF.R = S'.R := rfl
  rw [hSR] at he1
  rw [hS'R] at he2
  omega

/-! ## Single-step core-graph projection and update batch -/

/-- Projection of post-update vertices back to pre-update vertices (maps split clone `v' ↦ v`). -/
def stepProj (u : Update) (x : ℕ) : ℕ :=
  match u with
  | .split v v' _ _ => if x = v' then v else x
  | _ => x

lemma stepProj_applyUpdate_eq {G : MGraph} (hG : G.IsValid) {u : Update}
    (hu : G.UpdateIsValid u) {e : ℕ} (heG : e ∈ G.E) (heG' : e ∈ (G.applyUpdate u).E) :
    stepProj u ((G.applyUpdate u).tail e) = G.tail e ∧
    stepProj u ((G.applyUpdate u).head e) = G.head e := by
  cases u with
  | delete _ => simp [stepProj, MGraph.applyUpdate]
  | insert e₀ a b =>
    have hne : e ≠ e₀ := fun h => hu.1 (h ▸ heG)
    simp [stepProj, MGraph.applyUpdate, Function.update_of_ne hne]
  | split v v' St Sh =>
    rcases hu with ⟨_, hv', _, _⟩
    have ht_ne : G.tail e ≠ v' := fun h => hv' (h ▸ (hG e heG).1)
    have hh_ne : G.head e ≠ v' := fun h => hv' (h ▸ (hG e heG).2)
    dsimp only [stepProj, MGraph.applyUpdate]
    constructor <;> split_ifs with h1 h2 <;> simp_all

/-- Parent root in `S.R` of a vertex `r' ∈ S'.R`. -/
noncomputable def parentRoot (S : LSFState) (u : Update) (r' : ℕ) : ℕ :=
  S.RF.root (stepProj u r')

/-- Forest edges of `S` deleted from `F` during `u` that survive in `S'.G`. -/
noncomputable def droppedForestSurv (S S' : LSFState) : Finset ℕ :=
  open Classical in
  (S.RF.F.E \ S'.RF.F.E) ∩ S'.G.E

/-- Surviving core edges whose new tail root is `r'`, assigned to move tail off `parentRoot S u r'`. -/
noncomputable def splitMoveSetT (S S' : LSFState) (_u : Update) (r' : ℕ) : Finset ℕ :=
  open Classical in
  ((S.G.E \ S.RF.F.E) ∩ (S'.G.E \ S'.RF.F.E)).filter fun e =>
    S'.RF.root (S'.G.tail e) = r'

/-- Surviving core edges whose new head root is `r'`, assigned to move head off `parentRoot S u r'`. -/
noncomputable def splitMoveSetH (S S' : LSFState) (_u : Update) (r' : ℕ) : Finset ℕ :=
  open Classical in
  ((S.G.E \ S.RF.F.E) ∩ (S'.G.E \ S'.RF.F.E)).filter fun e =>
    S'.RF.root (S'.G.head e) = r'

/-- Deletion prefix of `coreStepBatch S u`. -/
noncomputable def coreStepDeletes (S _S' : LSFState) (u : Update) : List Update :=
  open Classical in
  match u with
  | .delete e₀ => if e₀ ∈ S.G.E \ S.RF.F.E then [Update.delete e₀] else []
  | _ => []

/-- Insertion suffix of `coreStepBatch S u`. -/
noncomputable def coreStepInserts (S S' : LSFState) (u : Update) : List Update :=
  open Classical in
  let insU := match u with
    | .insert e₀ a b => [Update.insert e₀ (S'.RF.root a) (S'.RF.root b)]
    | _ => []
  let insDrop := (droppedForestSurv S S').toList.map fun e =>
    Update.insert e (S'.RF.root (S'.G.tail e)) (S'.RF.root (S'.G.head e))
  insU ++ insDrop

/-- Explicit single-step update batch on `coreGraph S.G S.lsf` realizing `applyLSFUpdate S u`. -/
noncomputable def coreStepBatch (S : LSFState) (u : Update) : List Update :=
  open Classical in
  let S' := applyLSFUpdate S u
  let dels := coreStepDeletes S S' u
  let newRoots := (S'.R \ S.R).toList
  let splits := newRoots.map fun r' =>
    Update.split (parentRoot S u r') r' (splitMoveSetT S S' u r') (splitMoveSetH S S' u r')
  let ins := coreStepInserts S S' u
  dels ++ splits ++ ins

/-- Multi-step core update batch corresponding to a dynamic graph batch `U`. -/
noncomputable def coreBatch : LSFState → List Update → List Update
  | _, [] => []
  | S, u :: U => coreStepBatch S u ++ coreBatch (applyLSFUpdate S u) U

/-! ## Core-graph single-step and batch correctness theorems -/

private lemma stepProj_root_V {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {S S' : LSFState} {u : Update}
    (hI' : LSFInv C_lsst ℓ₀ S') (hG'_eq : S'.G = S.G.applyUpdate u)
    (hu : S.G.UpdateIsValid u) {r' : ℕ} (hr' : r' ∈ S'.R) :
    stepProj u r' ∈ S.G.V := by
  have hr'_GV : r' ∈ S'.G.V := (lsfInv_R_sub_V hI') hr'
  cases u with
  | delete _ => rw [hG'_eq] at hr'_GV; exact hr'_GV
  | insert _ _ _ => rw [hG'_eq] at hr'_GV; exact hr'_GV
  | split v v' _ _ =>
    dsimp only [stepProj]
    split_ifs with hv'
    · exact hu.1
    · rw [hG'_eq] at hr'_GV
      simp only [MGraph.applyUpdate, Finset.mem_insert] at hr'_GV
      exact hr'_GV.resolve_left hv'

/-- For a valid update `u` on `S.G`, `coreStepBatch S u` is valid on `coreGraph S.G S.lsf`
and produces a graph `GraphEq` to `coreGraph (applyLSFUpdate S u).G (applyLSFUpdate S u).lsf`. -/
theorem coreStepBatch_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState} {u : Update}
    (hI : LSFInv C_lsst ℓ₀ S) (hu : S.G.UpdateIsValid u) :
    let S' := applyLSFUpdate S u
    let C := coreGraph S.G S.lsf
    C.BatchIsValid (coreStepBatch S u) ∧
    GraphEq (C.applyBatch (coreStepBatch S u)) (coreGraph S'.G S'.lsf) := by
  classical
  have hInv' := applyLSFUpdate_inv hI hu
  rcases hInv' with ⟨hI', hG'_eq, _, _, _, _, _, _, hR_sub, hFE_sub, _⟩
  intro S' C
  have hS_G : S.G.IsValid := hI.hG_val
  have hS_RF : S.RF.IsRootedSpanningForestOf S.G := lsfInv_to_RS hI
  have hS'_G : S'.G.IsValid := hI'.hG_val
  have hS'_RF : S'.RF.IsRootedSpanningForestOf S'.G := lsfInv_to_RS hI'
  have hC_val : C.IsValid := coreGraph_isValid hS_G hS_RF
  have hCV : C.V = S.R := rfl
  have hCE : C.E = S.G.E \ S.RF.F.E := rfl
  have hS_R : S.RF.R = S.R := rfl
  have hS'_R : S'.RF.R = S'.R := rfl
  have hProj_conn : ∀ {x y : ℕ}, S'.RF.F.Connected x y →
      S.RF.F.Connected (stepProj u x) (stepProj u y) := by
    intro x y ⟨P, hW⟩
    refine ⟨P, ?_⟩
    induction hW with
    | nil s => exact .nil (stepProj u s)
    | @cons a _ x₀ P₀ hxE hsrc _ ih =>
      have hxF : x₀.1 ∈ S.RF.F.E := hFE_sub hxE
      have hxG' : x₀.1 ∈ S'.G.E := hS'_RF.2.2.2.2.2.1 hxE
      have hxG : x₀.1 ∈ S.G.E := hS_RF.2.2.2.2.2.1 hxF
      have hend := stepProj_applyUpdate_eq hS_G hu hxG (hG'_eq ▸ hxG')
      have hSub' := hS'_RF.2.2.2.2.2.2 x₀.1 hxE
      have hSub := hS_RF.2.2.2.2.2.2 x₀.1 hxF
      have ht_eq' : S'.RF.F.tail x₀.1 = (S.G.applyUpdate u).tail x₀.1 := by rw [hSub'.1, ← hG'_eq]
      have hh_eq' : S'.RF.F.head x₀.1 = (S.G.applyUpdate u).head x₀.1 := by rw [hSub'.2, ← hG'_eq]
      have hte : S.RF.F.tail x₀.1 = stepProj u (S'.RF.F.tail x₀.1) := by
        rw [hSub.1, ← hend.1, ← ht_eq']
      have hhe : S.RF.F.head x₀.1 = stepProj u (S'.RF.F.head x₀.1) := by
        rw [hSub.2, ← hend.2, ← hh_eq']
      have hsrc_proj : S.RF.F.src x₀ = stepProj u a := by
        rw [← hsrc]
        rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.src, hte, hhe]
      have hdst_proj : S.RF.F.dst x₀ = stepProj u (S'.RF.F.dst x₀) := by
        rcases x₀ with ⟨e, _ | _⟩ <;> simp [MGraph.dst, hte, hhe]
      refine .cons hxF hsrc_proj ?_
      simpa [hdst_proj] using ih
  have hroot_edge : ∀ {x x' : ℕ}, x ∈ S.G.V → x' ∈ S'.G.V → stepProj u x' = x →
      (S'.RF.root x' ∈ S.R ∧ S'.RF.root x' = S.RF.root x) ∨
      (S'.RF.root x' ∈ S'.R \ S.R ∧ parentRoot S u (S'.RF.root x') = S.RF.root x) := by
    intro x x' hx hx' hproj
    have hsp' := rootedForest_root_spec hS'_RF hx'
    have hconn : S.RF.F.Connected x (stepProj u (S'.RF.root x')) := by
      rw [← hproj]; exact hProj_conn hsp'.2
    have hr'_sub : S'.RF.root x' ∈ S'.R := hS'_R ▸ hsp'.1
    have hsp'_V : stepProj u (S'.RF.root x') ∈ S.G.V := stepProj_root_V hI' hG'_eq hu hr'_sub
    by_cases hrS : S'.RF.root x' ∈ S.R
    · left
      have hstep : stepProj u (S'.RF.root x') = S'.RF.root x' := by
        cases u with
        | delete _ => rfl
        | insert _ _ _ => rfl
        | split _ v' _ _ =>
          have hne : S'.RF.root x' ≠ v' := fun h => hu.2.1 (h ▸ (lsfInv_R_sub_V hI) hrS)
          simp [stepProj, hne]
      rw [hstep] at hconn
      refine ⟨hrS, (rootedForest_root_eq_of_mem hS_RF hx (hS_R ▸ hrS) hconn).symm⟩
    · right
      refine ⟨Finset.mem_sdiff.mpr ⟨hr'_sub, hrS⟩, ?_⟩
      dsimp only [parentRoot]
      exact (rootedForest_root_eq_iff hS_RF hsp'_V hx).mpr (connected_symm hconn)
  let delU := match u with
    | .delete e₀ => if e₀ ∈ C.E then [e₀] else []
    | _ => []
  let delU := match u with
    | .delete e₀ => if e₀ ∈ C.E then [e₀] else []
    | _ => []
  have hdelAll_nd : delU.Nodup := by
    cases u with
    | delete e₀ => dsimp only [delU]; split_ifs <;> simp
    | insert _ _ _ => simp [delU]
    | split _ _ _ _ => simp [delU]
  have hdelAll_sub : ∀ e ∈ delU, e ∈ C.E := by
    intro e he
    cases u with
    | delete e₀ =>
      dsimp only [delU] at he
      split_ifs at he with hmem
      · rw [List.mem_singleton.mp he]; exact hmem
      · simp at he
    | insert _ _ _ => simp [delU] at he
    | split _ _ _ _ => simp [delU] at he
  have hDels_eq : coreStepDeletes S S' u = delU.map Update.delete := by
    unfold coreStepDeletes delU
    cases u with
    | delete e₀ =>
      dsimp only
      change (if e₀ ∈ C.E then [Update.delete e₀] else []) = _
      split_ifs <;> simp
    | insert _ _ _ => rfl
    | split _ _ _ _ => rfl
  have hDels := applyUpdate_delete_list_spec hC_val hdelAll_nd hdelAll_sub
  rw [← hDels_eq] at hDels
  rcases hDels with ⟨hDels_BV, hDels_V, hDels_E, hDels_Ends, hDels_Val⟩
  set C₁ := C.applyBatch (coreStepDeletes S S' u)
  let newRoots := (S'.R \ S.R).toList
  have hnr_nd : newRoots.Nodup := Finset.nodup_toList _
  have hnr_disj : ∀ r ∈ newRoots, r ∉ C₁.V := by
    intro r hr hmem
    rw [hDels_V, hCV] at hmem
    exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hr)).2 hmem
  have hparent_mem : ∀ r ∈ newRoots, parentRoot S u r ∈ C₁.V := by
    intro r hr
    rw [hDels_V, hCV]
    have hrS' := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hr)).1
    exact hS_R ▸ (rootedForest_root_spec hS_RF (stepProj_root_V hI' hG'_eq hu hrS')).1
  let targetT : ℕ → ℕ := fun e => S'.RF.root (S'.G.tail e)
  let targetH : ℕ → ℕ := fun e => S'.RF.root (S'.G.head e)
  have hC₁E_mem : ∀ e ∈ C₁.E,
      e ∈ S.G.E \ S.RF.F.E ∧ e ∈ S'.G.E \ S'.RF.F.E := by
    intro e he
    rw [hDels_E, Finset.mem_sdiff] at he
    have heCE : e ∈ S.G.E \ S.RF.F.E := he.1
    have hnotU : e ∉ delU := fun h => he.2 (List.mem_toFinset.mpr h)
    have heSG : e ∈ S.G.E := (Finset.mem_sdiff.mp heCE).1
    have henl : e ∉ S'.RF.F.E := fun hf => (Finset.mem_sdiff.mp heCE).2 (hFE_sub hf)
    have heS'G : e ∈ S'.G.E := by
      rw [hG'_eq]
      cases u with
      | delete e₀ =>
        refine Finset.mem_erase.mpr ⟨fun h => ?_, heSG⟩
        have he₀_del : e₀ ∈ delU := by
          have he₀C : e₀ ∈ C.E := by rw [hCE, ← h]; exact heCE
          simp [delU, he₀C]
        exact hnotU (h ▸ he₀_del)
      | insert _ _ _ => exact Finset.mem_insert_of_mem heSG
      | split _ _ _ _ => exact heSG
    exact ⟨heCE, Finset.mem_sdiff.mpr ⟨heS'G, henl⟩⟩
  have hspecT : ∀ e ∈ C₁.E,
      (targetT e ∈ C₁.V ∧ targetT e = C₁.tail e) ∨
      (targetT e ∈ newRoots ∧ parentRoot S u (targetT e) = C₁.tail e) := by
    intro e he
    obtain ⟨heC, heC'⟩ := hC₁E_mem e he
    have heSG := (Finset.mem_sdiff.mp heC).1
    have heS'G := (Finset.mem_sdiff.mp heC').1
    have ht_eq : C₁.tail e = S.RF.root (S.G.tail e) := (hDels_Ends e he).1
    have hproj : stepProj u (S'.G.tail e) = S.G.tail e := by
      have hp := (stepProj_applyUpdate_eq hS_G hu heSG (hG'_eq ▸ heS'G)).1
      rw [← hG'_eq] at hp; exact hp
    rcases hroot_edge (hS_G e heSG).1 (hS'_G e heS'G).1 hproj with h1 | h2
    · left; exact ⟨hDels_V ▸ hCV ▸ h1.1, h1.2.trans ht_eq.symm⟩
    · right; exact ⟨Finset.mem_toList.mpr h2.1, h2.2.trans ht_eq.symm⟩
  have hspecH : ∀ e ∈ C₁.E,
      (targetH e ∈ C₁.V ∧ targetH e = C₁.head e) ∨
      (targetH e ∈ newRoots ∧ parentRoot S u (targetH e) = C₁.head e) := by
    intro e he
    obtain ⟨heC, heC'⟩ := hC₁E_mem e he
    have heSG := (Finset.mem_sdiff.mp heC).1
    have heS'G := (Finset.mem_sdiff.mp heC').1
    have hh_eq : C₁.head e = S.RF.root (S.G.head e) := (hDels_Ends e he).2
    have hproj : stepProj u (S'.G.head e) = S.G.head e := by
      have hp := (stepProj_applyUpdate_eq hS_G hu heSG (hG'_eq ▸ heS'G)).2
      rw [← hG'_eq] at hp; exact hp
    rcases hroot_edge (hS_G e heSG).2 (hS'_G e heS'G).2 hproj with h1 | h2
    · left; exact ⟨hDels_V ▸ hCV ▸ h1.1, h1.2.trans hh_eq.symm⟩
    · right; exact ⟨Finset.mem_toList.mpr h2.1, h2.2.trans hh_eq.symm⟩
  have hSplitSpec := applyUpdate_split_list_spec hDels_Val hnr_nd hnr_disj hparent_mem
    hspecT hspecH
  have hSplitFilterT_eq : ∀ r ∈ newRoots,
      C₁.E.filter (fun e => targetT e = r) = splitMoveSetT S S' u r := by
    intro r _
    ext e
    simp only [Finset.mem_filter, splitMoveSetT, Finset.mem_inter]
    constructor
    · rintro ⟨he, hTr⟩
      obtain ⟨heC, heC'⟩ := hC₁E_mem e he
      exact ⟨⟨heC, heC'⟩, hTr⟩
    · rintro ⟨⟨heC, heC'⟩, hTr⟩
      refine ⟨?_, hTr⟩
      rw [hDels_E, Finset.mem_sdiff]
      refine ⟨heC, fun hmem => ?_⟩
      rw [List.mem_toFinset] at hmem
      cases u with
      | delete e₀ =>
        dsimp only [delU] at hmem
        split_ifs at hmem with hmem'
        · rw [List.mem_singleton.mp hmem, Finset.mem_sdiff, hG'_eq] at heC'
          simp [MGraph.applyUpdate] at heC'
        · simp at hmem
      | insert _ _ _ => simp [delU] at hmem
      | split _ _ _ _ => simp [delU] at hmem
  have hSplitFilterH_eq : ∀ r ∈ newRoots,
      C₁.E.filter (fun e => targetH e = r) = splitMoveSetH S S' u r := by
    intro r _
    ext e
    simp only [Finset.mem_filter, splitMoveSetH, Finset.mem_inter]
    constructor
    · rintro ⟨he, hHr⟩
      obtain ⟨heC, heC'⟩ := hC₁E_mem e he
      exact ⟨⟨heC, heC'⟩, hHr⟩
    · rintro ⟨⟨heC, heC'⟩, hHr⟩
      refine ⟨?_, hHr⟩
      rw [hDels_E, Finset.mem_sdiff]
      refine ⟨heC, fun hmem => ?_⟩
      rw [List.mem_toFinset] at hmem
      cases u with
      | delete e₀ =>
        dsimp only [delU] at hmem
        split_ifs at hmem with hmem'
        · rw [List.mem_singleton.mp hmem, Finset.mem_sdiff, hG'_eq] at heC'
          simp [MGraph.applyUpdate] at heC'
        · simp at hmem
      | insert _ _ _ => simp [delU] at hmem
      | split _ _ _ _ => simp [delU] at hmem
  let splits := newRoots.map fun r' =>
    Update.split (parentRoot S u r') r' (splitMoveSetT S S' u r') (splitMoveSetH S S' u r')
  have hsplits_congr :
      newRoots.map (fun r' => Update.split (parentRoot S u r') r'
        (C₁.E.filter fun e => targetT e = r')
        (C₁.E.filter fun e => targetH e = r')) = splits :=
    List.map_congr_left fun r hr => by rw [hSplitFilterT_eq r hr, hSplitFilterH_eq r hr]
  rw [hsplits_congr] at hSplitSpec
  rcases hSplitSpec with ⟨hSp_BV, hSp_V, hSp_E, hSp_Ends, hSp_Val⟩
  set C₂ := C₁.applyBatch splits
  have hC₂V : C₂.V = S'.R := by
    rw [hSp_V, hDels_V, hCV]
    ext v
    simp only [newRoots, Finset.mem_union, List.mem_toFinset, Finset.mem_toList, Finset.mem_sdiff]
    constructor
    · rintro (hv | ⟨hv, _⟩) <;> [exact hR_sub hv; exact hv]
    · intro hv
      by_cases hvS : v ∈ S.R <;> [exact Or.inl hvS; exact Or.inr ⟨hv, hvS⟩]
  let insU_pairs := match u with
    | .insert e₀ a b => [(e₀, S'.RF.root a, S'.RF.root b)]
    | _ => []
  let insDrop_pairs := (droppedForestSurv S S').toList.map fun e =>
    (e, S'.RF.root (S'.G.tail e), S'.RF.root (S'.G.head e))
  let insPairs := insU_pairs ++ insDrop_pairs
  have hinsPairs_nd : (insPairs.map Prod.fst).Nodup := by
    rw [List.map_append, List.nodup_append]
    refine ⟨?_, ?_, ?_⟩
    · cases u <;> simp [insU_pairs]
    · simpa [insDrop_pairs, List.map_map, Function.comp_def] using
        (Finset.nodup_toList (droppedForestSurv S S'))
    · intro x hxU y hyD hxy
      subst hxy
      cases u with
      | insert e₀ _ _ =>
        simp only [insU_pairs, List.map_cons, List.map_nil, List.mem_singleton] at hxU
        subst hxU
        simp only [insDrop_pairs, List.map_map, List.mem_map, Function.comp_def] at hyD
        obtain ⟨z, hz, rfl⟩ := hyD
        have hzF := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_toList.mp hz)).1).1
        exact hu.1 (hS_RF.2.2.2.2.2.1 hzF)
      | delete _ => simp [insU_pairs] at hxU
      | split _ _ _ _ => simp [insU_pairs] at hxU
  have hinsPairs_notin : ∀ t ∈ insPairs, t.1 ∉ C₂.E := by
    intro t ht hmem
    rw [hSp_E, hDels_E, Finset.mem_sdiff] at hmem
    rw [List.mem_append] at ht
    rcases ht with htU | htD
    · cases u with
      | insert e₀ _ _ =>
        simp only [insU_pairs, List.mem_singleton] at htU
        rw [htU] at hmem
        exact hu.1 (Finset.mem_sdiff.mp hmem.1).1
      | delete _ => simp [insU_pairs] at htU
      | split _ _ _ _ => simp [insU_pairs] at htU
    · rw [List.mem_map] at htD
      obtain ⟨e, he, rfl⟩ := htD
      have heF := (Finset.mem_sdiff.mp (Finset.mem_inter.mp (Finset.mem_toList.mp he)).1).1
      exact (Finset.mem_sdiff.mp hmem.1).2 heF
  have hinsPairs_ends : ∀ t ∈ insPairs, t.2.1 ∈ C₂.V ∧ t.2.2 ∈ C₂.V := by
    intro t ht
    rw [hC₂V]
    rw [List.mem_append] at ht
    rcases ht with htU | htD
    · cases u with
      | insert e₀ a b =>
        simp only [insU_pairs, List.mem_singleton] at htU
        rw [htU]
        have ha' : a ∈ S'.G.V := hG'_eq ▸ hu.2.1
        have hb' : b ∈ S'.G.V := hG'_eq ▸ hu.2.2
        exact ⟨hS'_R ▸ (rootedForest_root_spec hS'_RF ha').1,
          hS'_R ▸ (rootedForest_root_spec hS'_RF hb').1⟩
      | delete _ => simp [insU_pairs] at htU
      | split _ _ _ _ => simp [insU_pairs] at htU
    · rw [List.mem_map] at htD
      obtain ⟨e, he, rfl⟩ := htD
      have heS' := (Finset.mem_inter.mp (Finset.mem_toList.mp he)).2
      exact ⟨hS'_R ▸ (rootedForest_root_spec hS'_RF (hS'_G e heS').1).1,
        hS'_R ▸ (rootedForest_root_spec hS'_RF (hS'_G e heS').2).1⟩
  have hInsSpec := applyUpdate_insert_list_spec hSp_Val hinsPairs_nd hinsPairs_notin hinsPairs_ends
  have hIns_eq : coreStepInserts S S' u = insPairs.map fun t => Update.insert t.1 t.2.1 t.2.2 := by
    unfold coreStepInserts insPairs insU_pairs insDrop_pairs
    cases u <;> simp [List.map_map, Function.comp_def]
  rw [← hIns_eq] at hInsSpec
  rcases hInsSpec with ⟨hIns_BV, hIns_V, hIns_E, hIns_Old, hIns_New, _⟩
  have hBatchEq : coreStepBatch S u = coreStepDeletes S S' u ++ splits ++ coreStepInserts S S' u := rfl
  simp only [hBatchEq, batchIsValid_append, applyBatch_append]
  refine ⟨⟨⟨hDels_BV, hSp_BV⟩, hIns_BV⟩, ?_⟩
  set C₃ := C₂.applyBatch (coreStepInserts S S' u)
  have hC₃V : C₃.V = S'.R := hIns_V.trans hC₂V
  have hC₃E : C₃.E = S'.G.E \ S'.RF.F.E := by
    rw [hIns_E, hSp_E, hDels_E]
    ext e
    simp only [Finset.mem_union, List.mem_toFinset, List.mem_map, insPairs]
    constructor
    · rintro (heD | ⟨t, ht, rfl⟩)
      · rw [Finset.mem_sdiff] at heD
        obtain ⟨heC, hndel⟩ := heD
        have heC_mem : e ∈ C.E := heC
        rw [hCE, Finset.mem_sdiff] at heC
        obtain ⟨heS, henF⟩ := heC
        have henF' : e ∉ S'.RF.F.E := fun hf => henF (hFE_sub hf)
        refine Finset.mem_sdiff.mpr ⟨?_, henF'⟩
        rw [hG'_eq]
        cases u with
        | delete e₀ =>
          refine Finset.mem_erase.mpr ⟨fun he₀ => ?_, heS⟩
          apply hndel
          rw [List.mem_toFinset]
          subst he₀
          simp [delU, heC_mem]
        | insert _ _ _ => exact Finset.mem_insert_of_mem heS
        | split _ _ _ _ => exact heS
      · rw [List.mem_append] at ht
        rcases ht with htU | htD
        · cases u with
          | insert e₀ _ _ =>
            simp only [insU_pairs, List.mem_singleton] at htU
            subst htU
            dsimp only
            refine Finset.mem_sdiff.mpr ⟨?_, fun hf => hu.1 (hS_RF.2.2.2.2.2.1 (hFE_sub hf))⟩
            rw [hG'_eq]; exact Finset.mem_insert_self _ _
          | delete _ => simp [insU_pairs] at htU
          | split _ _ _ _ => simp [insU_pairs] at htU
        · rw [List.mem_map] at htD
          obtain ⟨z, hz, rfl⟩ := htD
          have hmem := Finset.mem_inter.mp (Finset.mem_toList.mp hz)
          exact Finset.mem_sdiff.mpr ⟨hmem.2, (Finset.mem_sdiff.mp hmem.1).2⟩
    · intro heC'
      obtain ⟨heS'G, henF'⟩ := Finset.mem_sdiff.mp heC'
      by_cases heF : e ∈ S.RF.F.E
      · right
        refine ⟨(e, S'.RF.root (S'.G.tail e), S'.RF.root (S'.G.head e)), ?_, rfl⟩
        refine List.mem_append_right _ (List.mem_map.mpr ⟨e, ?_, rfl⟩)
        exact Finset.mem_toList.mpr (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨heF, henF'⟩, heS'G⟩)
      · cases u with
        | delete e₀ =>
          rw [hG'_eq] at heS'G
          obtain ⟨hne, heS⟩ := Finset.mem_erase.mp heS'G
          left
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨heS, heF⟩, fun hmem => ?_⟩
          rw [List.mem_toFinset] at hmem
          simp only [delU] at hmem
          split_ifs at hmem <;> simp_all
        | insert e₀ a b =>
          rw [hG'_eq] at heS'G
          rcases Finset.mem_insert.mp heS'G with rfl | heS
          · right
            refine ⟨(e, S'.RF.root a, S'.RF.root b),
              List.mem_append_left _ (by simp [insU_pairs]), rfl⟩
          · left
            refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨heS, heF⟩, fun hmem => ?_⟩
            rw [List.mem_toFinset] at hmem
            simp [delU] at hmem
        | split _ _ _ _ =>
          rw [hG'_eq] at heS'G
          left
          refine Finset.mem_sdiff.mpr ⟨Finset.mem_sdiff.mpr ⟨heS'G, heF⟩, fun hmem => ?_⟩
          rw [List.mem_toFinset] at hmem
          simp [delU] at hmem
  refine ⟨hC₃V.trans hS'_R.symm, hC₃E, fun e he => ?_⟩
  have heC' : e ∈ S'.G.E \ S'.RF.F.E := hC₃E ▸ he
  obtain ⟨heS'G, henF'⟩ := Finset.mem_sdiff.mp heC'
  change C₃.tail e = S'.RF.root (S'.G.tail e) ∧ C₃.head e = S'.RF.root (S'.G.head e)
  by_cases heF : e ∈ S.RF.F.E
  · have hm : (e, S'.RF.root (S'.G.tail e), S'.RF.root (S'.G.head e)) ∈ insPairs :=
      List.mem_append_right _ (List.mem_map.mpr
        ⟨e, Finset.mem_toList.mpr (Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨heF, henF'⟩, heS'G⟩), rfl⟩)
    exact hIns_New _ hm
  · by_cases hC₂ : e ∈ C₂.E
    · have h1 := hIns_Old e hC₂
      rw [hSp_E] at hC₂
      exact ⟨h1.1.trans (hSp_Ends e hC₂).1, h1.2.trans (hSp_Ends e hC₂).2⟩
    · cases u with
      | insert e₀ a b =>
        have he₀ : e = e₀ := by
          by_contra hne
          rw [hG'_eq] at heS'G
          have heS : e ∈ S.G.E := (Finset.mem_insert.mp heS'G).resolve_left hne
          have heC₁ : e ∈ C₁.E := by
            rw [hDels_E, Finset.mem_sdiff]
            refine ⟨Finset.mem_sdiff.mpr ⟨heS, heF⟩, fun hmem => ?_⟩
            rw [List.mem_toFinset] at hmem
            simp [delU] at hmem
          exact hC₂ (hSp_E ▸ heC₁)
        subst he₀
        have hm : (e, S'.RF.root a, S'.RF.root b) ∈ insPairs :=
          List.mem_append_left _ (by simp [insU_pairs])
        have hnew := hIns_New _ hm
        have htS' : S'.G.tail e = a := by rw [hG'_eq]; simp [MGraph.applyUpdate, Function.update_self]
        have hhS' : S'.G.head e = b := by rw [hG'_eq]; simp [MGraph.applyUpdate, Function.update_self]
        exact ⟨hnew.1.trans (congrArg S'.RF.root htS'.symm),
          hnew.2.trans (congrArg S'.RF.root hhS'.symm)⟩
      | delete e₀ =>
        exfalso
        rw [hG'_eq] at heS'G
        obtain ⟨hne, heS⟩ := Finset.mem_erase.mp heS'G
        apply hC₂
        rw [hSp_E, hDels_E, Finset.mem_sdiff]
        refine ⟨Finset.mem_sdiff.mpr ⟨heS, heF⟩, fun hmem => ?_⟩
        rw [List.mem_toFinset] at hmem
        simp only [delU] at hmem
        split_ifs at hmem <;> simp_all
      | split _ _ _ _ =>
        exfalso
        rw [hG'_eq] at heS'G
        apply hC₂
        rw [hSp_E, hDels_E, Finset.mem_sdiff]
        refine ⟨Finset.mem_sdiff.mpr ⟨heS'G, heF⟩, fun hmem => ?_⟩
        rw [List.mem_toFinset] at hmem
        simp [delU] at hmem

/-! ## Recourse bound, batch induction, and `lemma_5_14` -/

/-- Exact single-step recourse bound for `coreStepBatch S u`:
`(coreStepBatch S u).length ≤ 1 + 2 * (S'.R \ S.R).card`. -/
lemma coreStepBatch_length_le {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} {S : LSFState} {u : Update}
    (hI : LSFInv C_lsst ℓ₀ S) (hu : S.G.UpdateIsValid u) :
    let S' := applyLSFUpdate S u
    (coreStepBatch S u).length ≤ 1 + 2 * (S'.R \ S.R).card := by
  classical
  have hInv' := applyLSFUpdate_inv hI hu
  rcases hInv' with ⟨hI', hG'_eq, _, _, _, _, _, _, hR_sub, hFE_sub, _⟩
  intro S'
  have hdiff := lsf_forest_diff_le_R_diff (lsfInv_to_RS hI) (lsfInv_to_RS hI') hG'_eq hu
    hR_sub hFE_sub
  have hdrop_le : (droppedForestSurv S S').card ≤ (S'.R \ S.R).card :=
    (Finset.card_le_card Finset.inter_subset_left).trans hdiff
  unfold coreStepBatch coreStepDeletes coreStepInserts
  dsimp only [S'] at hdrop_le ⊢
  simp only [List.length_append, List.length_map, Finset.length_toList]
  change _ ≤ _
  cases u with
  | delete e₀ =>
    dsimp only at *; split_ifs <;> simp <;> omega
  | insert _ _ _ =>
    dsimp only at *; simp; omega
  | split _ _ _ _ =>
    dsimp only at *; simp; omega

/-- Multi-step batch transition and recourse for `coreBatch S U` modulo `GraphEq`. -/
theorem coreBatch_spec {C_lsst : ℝ} {ℓ₀ : ℕ → ℝ} :
    ∀ (U : List Update) (S : LSFState) (C : MGraph),
      LSFInv C_lsst ℓ₀ S → S.G.BatchIsValid U → GraphEq C (coreGraph S.G S.lsf) →
      let S' := applyLSFBatch S U
      C.BatchIsValid (coreBatch S U) ∧
      GraphEq (C.applyBatch (coreBatch S U)) (coreGraph S'.G S'.lsf) ∧
      (coreBatch S U).length ≤ U.length + 2 * (S'.R \ S.R).card := by
  intro U
  induction U with
  | nil =>
    intro S C _ _ hEq
    refine ⟨trivial, hEq, by simp [coreBatch]⟩
  | cons u U ih =>
    intro S C hI ⟨hu, hU⟩ hEq
    have hStep := coreStepBatch_spec hI hu
    have hInv' := applyLSFUpdate_inv hI hu
    rcases hInv' with ⟨hI', hG'_eq, _, _, _, _, _, _, hR_sub₁, _, _⟩
    set S₁ := applyLSFUpdate S u
    have hU₁ : S₁.G.BatchIsValid U := hG'_eq.symm ▸ hU
    have hStepLen := coreStepBatch_length_le hI hu
    obtain ⟨hBV₂, hEq₂, hLen₂⟩ := ih S₁ (C.applyBatch (coreStepBatch S u)) hI' hU₁
      (graphEq_trans (graphEq_applyBatch hEq (coreStepBatch S u)) hStep.2)
    have hR_sub₂ : S₁.R ⊆ (applyLSFBatch S₁ U).R :=
      (applyLSFBatch_inv U hI' hU₁).2.2.2.2.2.2.2.2.1
    have hpart : (S₁.R \ S.R).card + ((applyLSFBatch S₁ U).R \ S₁.R).card =
        ((applyLSFBatch S₁ U).R \ S.R).card := by
      have h1 : (S₁.R \ S.R).card = S₁.R.card - S.R.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hR_sub₁]
      have h2 : ((applyLSFBatch S₁ U).R \ S₁.R).card = (applyLSFBatch S₁ U).R.card - S₁.R.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hR_sub₂]
      have h3 : ((applyLSFBatch S₁ U).R \ S.R).card = (applyLSFBatch S₁ U).R.card - S.R.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr (hR_sub₁.trans hR_sub₂)]
      have hc1 : S.R.card ≤ S₁.R.card := Finset.card_le_card hR_sub₁
      have hc2 : S₁.R.card ≤ (applyLSFBatch S₁ U).R.card := Finset.card_le_card hR_sub₂
      omega
    refine ⟨?_, ?_, ?_⟩
    · rw [show coreBatch S (u :: U) = coreStepBatch S u ++ coreBatch S₁ U from rfl, batchIsValid_append]
      exact ⟨(graphEq_batchIsValid hEq _).mpr hStep.1, hBV₂⟩
    · rw [show coreBatch S (u :: U) = coreStepBatch S u ++ coreBatch S₁ U from rfl, applyBatch_append]
      exact hEq₂
    · simp only [coreBatch, List.length_append, List.length_cons]
      have hS_cons : applyLSFBatch S (u :: U) = applyLSFBatch S₁ U := rfl
      change (coreStepBatch S u).length + (coreBatch S₁ U).length ≤
        U.length + 1 + 2 * ((applyLSFBatch S (u :: U)).R \ S.R).card
      rw [hS_cons]
      change (coreStepBatch S u).length ≤ 1 + 2 * (S₁.R \ S.R).card at hStepLen
      change (coreBatch S₁ U).length ≤ _ at hLen₂
      omega

/-- **Lemma 5.14 (`jtree.tex` pp. 22–23)** over an online sequence of valid batches `U 1, …, U τ`:
maintains a sequence of core graphs `C 0, …, C τ` with exact `coreBatch` transitions, `GraphEq` to
`coreGraph (S t).G (S t).lsf`, cumulative recourse `q_C ≤ q + 112 * q * log²(n₀ + 2)`,
and `lemma_2_1` cumulative encoding size `≤ 20 * (C₀.m + q_C) * log(C₀.m + q_C + 2)`. -/
theorem lemma_5_14 (oracle : MGraph → (ℕ → ℝ) → (ℕ → ℝ) → MGraph) (C_lsst : ℝ)
    (hLSST : HasLSSTSpec oracle C_lsst)
    (G₀ : MGraph) (hG₀ : G₀.IsValid) (hV₀ : G₀.V.Nonempty)
    {ℓ₀ : ℕ → ℝ} (hℓ₀ : ∀ e ∈ G₀.E, 0 < ℓ₀ e)
    {v_init : ℕ → ℝ} (hv_init : ∀ e ∈ G₀.E, 0 < v_init e)
    (k : ℝ) (hk : 1 ≤ k)
    (U : ℕ → List Update) (τ : ℕ)
    (hBV : ∀ t ∈ Finset.Icc 1 τ,
      (List.foldl MGraph.applyBatch G₀ ((List.range (t - 1)).map (fun i => U (i + 1)))).BatchIsValid (U t)) :
    let S₀ := initLSF oracle C_lsst G₀ ℓ₀ v_init k
    let S : ℕ → LSFState := Nat.rec S₀ (fun t St => applyLSFBatch St (U (t + 1)))
    let UC : ℕ → List Update := fun t => coreBatch (S (t - 1)) (U t)
    let C : ℕ → MGraph := Nat.rec (coreGraph S₀.G S₀.lsf) (fun t Ct => Ct.applyBatch (UC (t + 1)))
    let q : ℕ := ∑ t ∈ Finset.Icc 1 τ, (U t).length
    let q_C : ℕ := ∑ t ∈ Finset.Icc 1 τ, (UC t).length
    (∀ t ≤ τ, LSFInv C_lsst ℓ₀ (S t) ∧
      (S t).G = List.foldl MGraph.applyBatch G₀ ((List.range t).map (fun i => U (i + 1))) ∧
      GraphEq (C t) (coreGraph (S t).G (S t).lsf) ∧ (C t).IsValid) ∧
    (∀ t ∈ Finset.Icc 1 τ, (C (t - 1)).BatchIsValid (UC t)) ∧
    (q_C : ℝ) ≤ (q : ℝ) + 112 * (q : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 ∧
    (∑ t ∈ Finset.Icc 1 τ, ((C (t - 1)).batchEnc (UC t) : ℝ)) ≤
      20 * (((C 0).m : ℝ) + (q_C : ℝ)) * Real.log (((C 0).m : ℝ) + (q_C : ℝ) + 2) := by
  intro S₀ S UC C q q_C
  have hS₀_inv := initLSF_inv hLSST hG₀ hV₀ hℓ₀ hv_init hk
  have hS₀_sp := initLSF_spec hLSST hG₀ hV₀ hℓ₀ hv_init hk
  have hS₀_G : S₀.G = G₀ := hS₀_sp.2.1
  have hS₀_G₀ : S₀.G₀ = G₀ := hS₀_sp.1
  have hPrefix : ∀ t ≤ τ,
      LSFInv C_lsst ℓ₀ (S t) ∧
      (S t).G = List.foldl MGraph.applyBatch G₀ ((List.range t).map (fun i => U (i + 1))) ∧
      GraphEq (C t) (coreGraph (S t).G (S t).lsf) ∧
      (C t).IsValid ∧
      (S t).G₀ = G₀ := by
    intro t
    induction t with
    | zero =>
      intro _
      have hC₀_val : (C 0).IsValid := coreGraph_isValid hS₀_inv.hG_val (lsfInv_to_RS hS₀_inv)
      refine ⟨hS₀_inv, by simp [S, S₀, hS₀_G], graphEq_refl _, hC₀_val, hS₀_G₀⟩
    | succ t ih =>
      intro ht
      obtain ⟨hIt, hGt, hEqt, _, hG₀t⟩ := ih (Nat.le_of_succ_le ht)
      have ht_mem : t + 1 ∈ Finset.Icc 1 τ := Finset.mem_Icc.mpr ⟨Nat.succ_pos t, ht⟩
      have hBV_t : (S t).G.BatchIsValid (U (t + 1)) := by
        rw [hGt]
        simpa [Nat.add_sub_cancel] using hBV (t + 1) ht_mem
      have hStep_inv := applyLSFBatch_inv (U (t + 1)) hIt hBV_t
      have hCb := coreBatch_spec (U (t + 1)) (S t) (C t) hIt hBV_t hEqt
      have hSt1_G : (S (t + 1)).G =
          List.foldl MGraph.applyBatch G₀ ((List.range (t + 1)).map (fun i => U (i + 1))) := by
        change (applyLSFBatch (S t) (U (t + 1))).G = _
        rw [hStep_inv.2.1, hGt, List.range_succ, List.map_append, List.map_singleton,
          List.foldl_append, List.foldl_cons, List.foldl_nil]
      have hcore_val := coreGraph_isValid hStep_inv.1.hG_val
        (show (applyLSFBatch (S t) (U (t + 1))).lsf.F.IsRootedSpanningForestOf
          (applyLSFBatch (S t) (U (t + 1))).G from lsfInv_to_RS hStep_inv.1)
      have hVal_next : (C (t + 1)).IsValid := graphEq_isValid (graphEq_symm hCb.2.1) hcore_val
      exact ⟨hStep_inv.1, hSt1_G, hCb.2.1, hVal_next, hStep_inv.2.2.1.trans hG₀t⟩
  have hStepBounds : ∀ t ∈ Finset.Icc 1 τ,
      (C (t - 1)).BatchIsValid (UC t) ∧
      ((UC t).length : ℝ) ≤ ((U t).length : ℝ) +
        2 * (((S t).R.card : ℝ) - ((S (t - 1)).R.card : ℝ)) := by
    intro t ht
    rw [Finset.mem_Icc] at ht
    obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
    have hk_le : k ≤ τ := by omega
    obtain ⟨hIk, hGk, hEqk, _, _⟩ := hPrefix k hk_le
    have hBV_k : (S k).G.BatchIsValid (U (k + 1)) := by
      rw [hGk]
      simpa [Nat.add_sub_cancel] using hBV (k + 1) (Finset.mem_Icc.mpr ht)
    have hCb := coreBatch_spec (U (k + 1)) (S k) (C k) hIk hBV_k hEqk
    have hInv_k1 := applyLSFBatch_inv (U (k + 1)) hIk hBV_k
    have hR_sub : (S k).R ⊆ (S (k + 1)).R := hInv_k1.2.2.2.2.2.2.2.2.1
    have hdiff : ((S (k + 1)).R \ (S k).R).card = (S (k + 1)).R.card - (S k).R.card := by
      rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hR_sub]
    have hlen_nat : (UC (k + 1)).length ≤ (U (k + 1)).length +
        2 * ((S (k + 1)).R \ (S k).R).card := hCb.2.2
    have hle_R : (S k).R.card ≤ (S (k + 1)).R.card := Finset.card_le_card hR_sub
    have hlen_real : ((UC (k + 1)).length : ℝ) ≤ ((U (k + 1)).length : ℝ) +
        2 * (((S (k + 1)).R.card : ℝ) - ((S k).R.card : ℝ)) := by
      have hcast_diff : (((S (k + 1)).R \ (S k).R).card : ℝ) =
          ((S (k + 1)).R.card : ℝ) - ((S k).R.card : ℝ) := by
        rw [hdiff, Nat.cast_sub hle_R]
      have hcast_len : ((UC (k + 1)).length : ℝ) ≤ ((U (k + 1)).length : ℝ) +
          2 * (((S (k + 1)).R \ (S k).R).card : ℝ) := by exact_mod_cast hlen_nat
      linarith
    exact ⟨hCb.1, hlen_real⟩
  have hGrowth_sum : ∀ m ≤ τ,
      ((S m).R.card : ℝ) - ((S 0).R.card : ℝ) ≤
        56 * ((∑ t ∈ Finset.Icc 1 m, (U t).length : ℕ) : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hm_le : m ≤ τ := Nat.le_of_succ_le hm
      obtain ⟨hIm, hGm, _, _, hG₀m⟩ := hPrefix m hm_le
      have hBV_m : (S m).G.BatchIsValid (U (m + 1)) := by
        rw [hGm]
        simpa [Nat.add_sub_cancel] using hBV (m + 1) (Finset.mem_Icc.mpr ⟨Nat.succ_pos m, hm⟩)
      have hInv_m1 := applyLSFBatch_inv (U (m + 1)) hIm hBV_m
      have hstep := hInv_m1.2.2.2.2.2.2.2.2.2.2
      rw [hG₀m] at hstep
      have hS_succ : S (m + 1) = applyLSFBatch (S m) (U (m + 1)) := rfl
      have hsum_split : ∑ t ∈ Finset.Icc 1 (m + 1), (U t).length =
          (∑ t ∈ Finset.Icc 1 m, (U t).length) + (U (m + 1)).length := by
        have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
          ext x; simp [Finset.mem_Icc]; omega
        rw [hIcc, Finset.sum_insert (by simp), add_comm]
      have ih' := ih hm_le
      push_cast at ih'
      rw [hS_succ, hsum_split]
      push_cast
      linarith
  have hTele : ∀ m ≤ τ,
      (∑ t ∈ Finset.Icc 1 m, (((S t).R.card : ℝ) - ((S (t - 1)).R.card : ℝ))) =
        ((S m).R.card : ℝ) - ((S 0).R.card : ℝ) := by
    intro m
    induction m with
    | zero => intro _; simp
    | succ m ih =>
      intro hm
      have hIcc : Finset.Icc 1 (m + 1) = insert (m + 1) (Finset.Icc 1 m) := by
        ext x; simp [Finset.mem_Icc]; omega
      rw [hIcc, Finset.sum_insert (by simp), ih (Nat.le_of_succ_le hm)]
      simp only [Nat.add_sub_cancel]
      ring
  have hqC_bound : (q_C : ℝ) ≤ (q : ℝ) + 112 * (q : ℝ) * (Real.log ((G₀.n : ℝ) + 2)) ^ 2 := by
    have hsum_step : ∑ t ∈ Finset.Icc 1 τ, ((UC t).length : ℝ) ≤
        ∑ t ∈ Finset.Icc 1 τ, (((U t).length : ℝ) +
          2 * (((S t).R.card : ℝ) - ((S (t - 1)).R.card : ℝ))) :=
      Finset.sum_le_sum fun t ht => (hStepBounds t ht).2
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hTele τ (le_refl τ)] at hsum_step
    have hGτ := hGrowth_sum τ (le_refl τ)
    push_cast at hGτ
    dsimp only [q_C, q]
    push_cast
    linarith
  have hEnc := lemma_2_1 (G := C) (U := UC) (τ := τ) (hPrefix 0 (Nat.zero_le τ)).2.2.2.1
    (fun t ht1 htτ => ⟨(hStepBounds t (Finset.mem_Icc.mpr ⟨ht1, htτ⟩)).1, by
      obtain ⟨k, rfl⟩ : ∃ k, t = k + 1 := Nat.exists_eq_succ_of_ne_zero (by omega)
      simp only [Nat.add_sub_cancel]
      rfl⟩)
  have hEnc_q : (∑ t ∈ Finset.Icc 1 τ, ((C (t - 1)).batchEnc (UC t) : ℝ)) ≤
      20 * (((C 0).m : ℝ) + (q_C : ℝ)) * Real.log (((C 0).m : ℝ) + (q_C : ℝ) + 2) := by
    simpa [q_C] using hEnc
  exact ⟨fun t ht => let h := hPrefix t ht; ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩,
    fun t ht => (hStepBounds t ht).1, hqC_bound, hEnc_q⟩

/-! ## Independent self-loop splitting & documentation of `coreLen` / `coreGrad` / `T_cur` -/

/-- Positive self-loop breaking theorem (`Update.split v v' St Sh` with independent `(St, Sh)`):
splitting vertex `0` to `1` with `St = ∅, Sh = {0}` directly separates a self-loop `(0, 0)` into
`(0, 1)` without deleting and reinserting edge `0`, whereas uniform `Update.split v v' S S` splits
always preserve `tail 0 = head 0`. -/
theorem coreGraph_split_selfLoop_breaks :
    (let C₀ : MGraph := { V := {0}, E := {0}, tail := fun _ => 0, head := fun _ => 0 }
     let C₁ := C₀.applyUpdate (.split 0 1 ∅ {0})
     C₀.UpdateIsValid (.split 0 1 ∅ {0}) ∧
       C₁.tail 0 = 0 ∧ C₁.head 0 = 1 ∧ C₁.tail 0 ≠ C₁.head 0) ∧
    (let C₀ : MGraph := { V := {0, 1}, E := {0}, tail := fun _ => 0, head := fun _ => 0 }
     ∀ (U : List Update), (∀ u ∈ U, ∃ v v' S, u = Update.split v v' S S) →
       (C₀.applyBatch U).tail 0 = (C₀.applyBatch U).head 0) := by
  refine ⟨?_, ?_⟩
  · refine ⟨⟨by simp, by simp, by simp, fun e he => by simp at he; exact Or.inr rfl⟩, ?_⟩
    simp [MGraph.applyUpdate]
  · intro C₀ U hsp
    have hgen : ∀ (G : MGraph) (V : List Update),
        G.tail 0 = G.head 0 → (∀ u ∈ V, ∃ v v' S, u = Update.split v v' S S) →
        (G.applyBatch V).tail 0 = (G.applyBatch V).head 0 := by
      intro G V h0 hV
      induction V generalizing G with
      | nil => exact h0
      | cons u V ih =>
        obtain ⟨v, v', S, rfl⟩ := hV u List.mem_cons_self
        refine ih (G.applyUpdate (.split v v' S S)) ?_ (fun x hx => hV x (List.mem_cons_of_mem _ hx))
        dsimp only [MGraph.applyUpdate]
        rw [h0]
    exact hgen C₀ U rfl hsp

/-- Documentation lemma: `S.lsf.T` is `S.T_cur` (maintaining edges `S.T₀.E`, while `S.RF.F` is
the decremental forest `T₀ \ droppedEdges`), whereas `coreLen` weights edges by `S.wstr e * ℓ e`
and `coreGrad` routes `g` via `treeRootPot S.T_cur g`. -/
lemma coreGraph_lsf_docs (S : LSFState) (ℓ g : ℕ → ℝ) (e : ℕ) :
    S.lsf.T = S.T_cur ∧
    S.lsf.F = S.RF ∧
    coreLen S.lsf ℓ e = S.wstr e * ℓ e ∧
    coreGrad S.G S.lsf g e = g e + treeRootPot S.T_cur g (S.G.head e) - treeRootPot S.T_cur g (S.G.tail e) :=
  ⟨rfl, rfl, rfl, rfl⟩

end MinCostFlow.SparseCore
