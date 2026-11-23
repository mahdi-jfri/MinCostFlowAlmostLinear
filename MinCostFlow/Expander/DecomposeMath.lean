module

public import WordRAM.Contract
public import MinCostFlow.Spanner.Layouts
public import MinCostFlow.Spanner.ToolContracts
public import MinCostFlow.Expander.DecomposeCompress

import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Mathematical Bridges for Word-RAM `Decompose` (Levels, `ℓ`, and Length Bounds)

Builds on `DecomposeCompress` to assemble:
1. Level correctness and `remG.m ≤ 2^(i - 1) * curG.n` from Word-RAM `uniqLabels` and `R_of`;
2. `Decompose.encode` length bound `≤ 4 + 5 * G.m` and level count `ℓ` bounds.
-/

@[expose] public section

namespace MinCostFlow.Expander

open Classical
open MinCostFlow.Cited MinCostFlow.Spanner

/-! ## 4. Level Assembly from Word-RAM `uniqLabels` and `R_of` -/

private lemma part_label_const {G : Cited.Graph} {label : List ℕ} {Y : Finset ℕ}
    (hY : Y ∈ Cited.partsOf G label) {z₁ z₂ : ℕ} (hz₁ : z₁ ∈ Y) (hz₂ : z₂ ∈ Y) :
    label.getD z₁ 0 = label.getD z₂ 0 := by
  unfold Cited.partsOf at hY
  rcases Finset.mem_image.mp hY with ⟨z, _, rfl⟩
  have h1 := (Finset.mem_filter.mp hz₁).2
  have h2 := (Finset.mem_filter.mp hz₂).2
  exact h1.trans h2.symm

lemma decomposeLevel_of_parts_spec {curG : Cited.Graph} {i : ℕ}
    (hV : curG.IsValid) (hL : curG.IsLoopless) (hi : 1 ≤ i)
    (hm_in : curG.m ≤ 2 ^ i * curG.n)
    {label : List ℕ} {φ_B1 φ_out : ℝ} (_hφ_out : 0 < φ_out)
    (_hdecExp : Cited.IsExpanderDecomposition (twinGraph (2 ^ i) curG) (1 / 200 : ℝ) φ_B1 label)
    (hdecCut : (((twinGraph (2 ^ i) curG).edges.filter
      fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length : ℝ) ≤
      (1 / 200 : ℝ) * ((twinGraph (2 ^ i) curG).m : ℝ))
    (uniqLabels : List ℕ) (huniq_nd : uniqLabels.Nodup)
    (huniq_covers : ∀ v < curG.n, label.getD (2 * v) 0 ∈ uniqLabels)
    (R_of : ℕ → Finset ℕ)
    (hpartSpec : ∀ L ∈ uniqLabels,
      let G_twin := twinGraph (2 ^ i) curG
      let Y_L := (Finset.range (2 * curG.n)).filter fun z => label.getD z 0 = L
      let X_L := partX curG.n Y_L
      R_of L ⊆ X_L ∧
      (R_of L = ∅ ∨
        (2 ≤ (R_of L).card ∧ curG.IsConductanceExpanderOn (R_of L) φ_out ∧
          ∀ v ∈ R_of L, φ_out * ((2 ^ i : ℕ) : ℝ) ≤ (curG.degIn (R_of L) v : ℝ))) ∧
      (curG.inside X_L).length - (curG.inside (R_of L)).length ≤ 15 * G_twin.cut Y_L) :
    let validRs := (uniqLabels.map R_of).filter fun R => decide (2 ≤ R.card)
    let pred : ℕ × ℕ → Bool := fun e => validRs.any fun R => decide (e.1 ∈ R ∧ e.2 ∈ R)
    let Gi : Cited.Graph := { n := curG.n, edges := curG.edges.filter pred }
    let remG : Cited.Graph := { n := curG.n, edges := curG.edges.filter fun e => !pred e }
    Gi.IsValid ∧ Gi.IsLoopless ∧ remG.IsValid ∧ remG.IsLoopless ∧
    (Gi.edges ++ remG.edges).Perm curG.edges ∧
    Gi.m ≤ 2 ^ i * curG.n ∧
    remG.m ≤ 2 ^ (i - 1) * curG.n ∧
    validRs.Pairwise Disjoint ∧
    (∀ R ∈ validRs,
      R ⊆ curG.verts ∧ 2 ≤ R.card ∧
      Gi.IsConductanceExpanderOn R φ_out ∧
      (∀ x ∈ R, φ_out * (2 : ℝ) ^ i ≤ (Gi.degIn R x : ℝ)) ∧
      (∀ e ∈ Gi.edges, e.1 ∈ R ↔ e.2 ∈ R)) ∧
    (∀ e ∈ Gi.edges, ∃ R ∈ validRs, e.1 ∈ R ∧ e.2 ∈ R) := by
  intro validRs pred Gi remG
  set G_twin := twinGraph (2 ^ i) curG
  let Y_of : ℕ → Finset ℕ := fun L => (Finset.range (2 * curG.n)).filter fun z => label.getD z 0 = L
  have hGiV : Gi.IsValid := fun e he => hV e (List.mem_filter.mp he).1
  have hGiL : Gi.IsLoopless := fun e he => hL e (List.mem_filter.mp he).1
  have hremV : remG.IsValid := fun e he => hV e (List.mem_filter.mp he).1
  have hremL : remG.IsLoopless := fun e he => hL e (List.mem_filter.mp he).1
  have hperm : (Gi.edges ++ remG.edges).Perm curG.edges := filter_comp_perm pred curG.edges
  have hGi_m : Gi.m ≤ 2 ^ i * curG.n := le_trans (List.length_filter_le _ _) hm_in
  have hparts_pw := partsOf_toList_pairwiseDisjoint G_twin label
  have hlist_sum_le : ∀ (f g : Finset ℕ → ℕ) (xs : List (Finset ℕ)),
      (∀ Y ∈ xs, f Y ≤ g Y) → (xs.map f).sum ≤ (xs.map g).sum := by
    intro f g xs hfg
    induction xs with
    | nil => simp
    | cons x rest ih =>
      simp only [List.map_cons, List.sum_cons]
      exact Nat.add_le_add (hfg x List.mem_cons_self)
        (ih fun y hy => hfg y (List.mem_cons_of_mem _ hy))
  have hrem_m : remG.m ≤ 2 ^ (i - 1) * curG.n := by
    set parts := (Cited.partsOf G_twin label).toList
    let RY : Finset ℕ → Finset ℕ := fun Y =>
      if h : ∃ v < curG.n, 2 * v ∈ Y then R_of (label.getD (2 * h.choose) 0) else ∅
    have hRY_spec : ∀ Y ∈ parts,
        let X := partX curG.n Y
        RY Y ⊆ X ∧ (curG.inside X).length - (curG.inside (RY Y)).length ≤ 15 * G_twin.cut Y := by
      intro Y hY
      have hY_mem : Y ∈ Cited.partsOf G_twin label := Finset.mem_toList.mp hY
      by_cases hex : ∃ v < curG.n, 2 * v ∈ Y
      · set v0 := hex.choose
        have hv0 : v0 < curG.n ∧ 2 * v0 ∈ Y := hex.choose_spec
        set L0 := label.getD (2 * v0) 0
        have hL0_uniq : L0 ∈ uniqLabels := huniq_covers v0 hv0.1
        have hY_eq : Y = Y_of L0 := by
          unfold Cited.partsOf at hY_mem
          rcases Finset.mem_image.mp hY_mem with ⟨z, _, rfl⟩
          have hz_eq : label.getD z 0 = L0 :=
            (Finset.mem_filter.mp hv0.2).2.symm
          ext w
          simp only [Y_of, G_twin, twinGraph, Cited.Graph.verts, Finset.mem_filter, Finset.mem_range]
          rw [hz_eq]
        have hRY_eq : RY Y = R_of L0 := by
          dsimp only [RY]; rw [dite_eq_left_of_eq_true (eq_true hex)]
        have hsp := hpartSpec L0 hL0_uniq
        dsimp only [Y_of] at hY_eq
        rw [← hY_eq] at hsp
        rw [hRY_eq]
        exact ⟨hsp.1, hsp.2.2⟩
      · have hXempty : partX curG.n Y = ∅ := by
          ext v
          simp only [partX, Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
          intro ⟨hv, h2v⟩
          exact hex ⟨v, hv, h2v⟩
        have hRY_eq : RY Y = ∅ := by
          dsimp only [RY]; rw [dite_eq_right_of_eq_false (eq_false hex)]
        rw [hXempty, hRY_eq]
        simp
    set crossE := (curG.edges.filter fun e => decide (label.getD (2 * e.1) 0 ≠ label.getD (2 * e.2) 0)).length
    set crossTwin := (G_twin.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length
    have hcross_le : crossE ≤ crossTwin := by
      have h1 : crossE = ((curG.edges.map fun (e : ℕ × ℕ) => (2 * e.1, 2 * e.2)).filter
          fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)).length := by
        simp [crossE, List.filter_map]; rfl
      rw [h1]
      change ((curG.edges.map fun (e : ℕ × ℕ) => (2 * e.1, 2 * e.2)).filter _).length ≤
        ((curG.edges.map (fun (e : ℕ × ℕ) => (2 * e.1, 2 * e.2)) ++
          (List.range curG.n).flatMap (fun u => List.replicate (2 ^ i) (2 * u, 2 * u + 1))).filter _).length
      rw [List.filter_append, List.length_append]
      exact Nat.le_add_right _ _
    have hrem_split : remG.m ≤ crossE +
        ((curG.edges.filter fun e =>
          decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) && !pred e)).length := by
      suffices h : ∀ E : List (ℕ × ℕ),
          (E.filter fun e => !pred e).length ≤
          (E.filter fun e => decide (label.getD (2 * e.1) 0 ≠ label.getD (2 * e.2) 0)).length +
          (E.filter fun e => decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) && !pred e).length by
        exact h curG.edges
      intro E
      induction E with
      | nil => simp
      | cons e es ih =>
        rw [List.filter_cons, List.filter_cons, List.filter_cons]
        cases hpe : pred e <;> cases hlbl : decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) <;>
          simp_all <;> omega
    have hin_parts :
        (curG.edges.filter fun e =>
          decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) && !pred e).length ≤
        (parts.map fun Y =>
          (curG.inside (partX curG.n Y)).length - (curG.inside (RY Y)).length).sum := by
      set Lsame := curG.edges.filter fun e =>
        decide (label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0) && !pred e
      let cond : Finset ℕ → ℕ × ℕ → Bool := fun Y e =>
        let X := partX curG.n Y
        let R := RY Y
        decide (e.1 ∈ X) && decide (e.2 ∈ X) && !(decide (e.1 ∈ R) && decide (e.2 ∈ R))
      have hLsame_any : Lsame = Lsame.filter (fun e => parts.any fun Y => cond Y e) := by
        refine (List.filter_eq_self.mpr ?_).symm
        intro e he
        have heLs : e ∈ curG.edges ∧ label.getD (2 * e.1) 0 = label.getD (2 * e.2) 0 ∧ pred e = false := by
          simpa [Lsame] using he
        rcases hV e heLs.1 with ⟨he1, he2⟩
        let Y0 := G_twin.verts.filter fun z => label.getD z 0 = label.getD (2 * e.1) 0
        have h2e1_verts : 2 * e.1 ∈ G_twin.verts := Finset.mem_range.mpr (by change 2 * e.1 < 2 * curG.n; omega)
        have h2e2_verts : 2 * e.2 ∈ G_twin.verts := Finset.mem_range.mpr (by change 2 * e.2 < 2 * curG.n; omega)
        have hY0_mem : Y0 ∈ Cited.partsOf G_twin label := Finset.mem_image.mpr ⟨2 * e.1, h2e1_verts, rfl⟩
        have hY0_parts : Y0 ∈ parts := Finset.mem_toList.mpr hY0_mem
        have he1X : e.1 ∈ partX curG.n Y0 :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he1, Finset.mem_filter.mpr ⟨h2e1_verts, rfl⟩⟩
        have he2X : e.2 ∈ partX curG.n Y0 :=
          Finset.mem_filter.mpr ⟨Finset.mem_range.mpr he2, Finset.mem_filter.mpr ⟨h2e2_verts, heLs.2.1.symm⟩⟩
        have hex0 : ∃ v < curG.n, 2 * v ∈ Y0 := ⟨e.1, he1, Finset.mem_filter.mpr ⟨h2e1_verts, rfl⟩⟩
        have hRY0_eq : RY Y0 = R_of (label.getD (2 * e.1) 0) := by
          have hchoose : label.getD (2 * hex0.choose) 0 = label.getD (2 * e.1) 0 :=
            part_label_const hY0_mem hex0.choose_spec.2 (Finset.mem_filter.mpr ⟨h2e1_verts, rfl⟩)
          dsimp only [RY]
          rw [dite_eq_left_of_eq_true (eq_true hex0), hchoose]
        have hL0_uniq : label.getD (2 * e.1) 0 ∈ uniqLabels := huniq_covers e.1 he1
        have hL0_spec := hpartSpec (label.getD (2 * e.1) 0) hL0_uniq
        have he_not_R : !(decide (e.1 ∈ RY Y0) && decide (e.2 ∈ RY Y0)) = true := by
          by_contra hf
          have hboth : e.1 ∈ RY Y0 ∧ e.2 ∈ RY Y0 := by simpa using hf
          rw [hRY0_eq] at hboth
          have hne_R : R_of (label.getD (2 * e.1) 0) ≠ ∅ := Finset.ne_empty_of_mem hboth.1
          have h2le : 2 ≤ (R_of (label.getD (2 * e.1) 0)).card := by
            rcases hL0_spec.2.1 with hem | ⟨hc, _, _⟩
            · exact False.elim (hne_R hem)
            · exact hc
          have hmem_valid : R_of (label.getD (2 * e.1) 0) ∈ validRs := by
            rw [List.mem_filter]
            exact ⟨List.mem_map.mpr ⟨_, hL0_uniq, rfl⟩, decide_eq_true h2le⟩
          have hpred_true : pred e = true := List.any_eq_true.mpr ⟨_, hmem_valid, by simpa using hboth⟩
          rw [heLs.2.2] at hpred_true
          simp at hpred_true
        have he_or : e.1 ∉ RY Y0 ∨ e.2 ∉ RY Y0 := by simpa using he_not_R
        exact List.any_eq_true.mpr ⟨Y0, hY0_parts, by simp [cond, he1X, he2X, he_or]⟩
      have hlen_sum := sum_filter_any_le Lsame cond parts
      rw [← hLsame_any] at hlen_sum
      refine le_trans hlen_sum ?_
      have hsub_le : ∀ Y ∈ parts, (Lsame.filter (cond Y)).length ≤
          (curG.inside (partX curG.n Y)).length - (curG.inside (RY Y)).length := by
        intro Y hY
        have h1 : (Lsame.filter (cond Y)).length ≤ (curG.edges.filter (cond Y)).length := by
          dsimp only [Lsame]
          rw [List.filter_comm]
          exact List.length_filter_le _ _
        have h2 : curG.edges.filter (cond Y) =
            (curG.inside (partX curG.n Y)).filter fun e => !(decide (e.1 ∈ RY Y) && decide (e.2 ∈ RY Y)) := by
          simp only [cond, Cited.Graph.inside, List.filter_filter]
          refine List.filter_congr fun e _ => ?_
          by_cases h1e : e.1 ∈ partX curG.n Y <;> by_cases h2e : e.2 ∈ partX curG.n Y <;> simp [h1e, h2e]
        rw [h2, inside_partX_diff_len curG (partX curG.n Y) (RY Y) (hRY_spec Y hY).1] at h1
        exact h1
      exact hlist_sum_le _ _ parts hsub_le
    have hsum15 : (parts.map fun Y =>
        (curG.inside (partX curG.n Y)).length - (curG.inside (RY Y)).length).sum ≤
        15 * (parts.map fun Y => G_twin.cut Y).sum := by
      have h1 : (parts.map fun Y =>
          (curG.inside (partX curG.n Y)).length - (curG.inside (RY Y)).length).sum ≤
          (parts.map fun Y => 15 * G_twin.cut Y).sum :=
        hlist_sum_le _ _ parts fun Y hY => (hRY_spec Y hY).2
      have h2 : ∀ (c : ℕ) (f : Finset ℕ → ℕ) (xs : List (Finset ℕ)),
          (xs.map fun Y => c * f Y).sum = c * (xs.map f).sum := by
        intro c f xs
        induction xs with
        | nil => simp
        | cons x rest ih => simp only [List.map_cons, List.sum_cons, ih]; ring
      rw [h2] at h1
      exact h1
    have hcut_sum_le : (parts.map fun Y => G_twin.cut Y).sum ≤ 2 * crossTwin := by
      have hTV := twinGraph_isValid (D := 2 ^ i) hV
      set Lc := G_twin.edges.filter fun e => decide (label.getD e.1 0 ≠ label.getD e.2 0)
      have hcut_eq : ∀ Y ∈ parts, G_twin.cut Y ≤
          (Lc.filter fun e => decide (e.1 ∈ Y)).length +
            (Lc.filter fun e => decide (e.2 ∈ Y)).length := by
        intro Y hY
        have hY_mem : Y ∈ Cited.partsOf G_twin label := Finset.mem_toList.mp hY
        change ((G_twin.inside G_twin.verts).filter
          fun e => decide (e.1 ∈ Y) != decide (e.2 ∈ Y)).length ≤ _
        have hins_eq : G_twin.inside G_twin.verts = G_twin.edges := by
          unfold Cited.Graph.inside
          exact List.filter_eq_self.mpr fun e he => by
            have hv : e.1 < G_twin.n ∧ e.2 < G_twin.n := hTV e he
            simp [Cited.Graph.verts, hv]
        have hsub : G_twin.edges.filter (fun e => decide (e.1 ∈ Y) != decide (e.2 ∈ Y)) =
            Lc.filter (fun e => decide (e.1 ∈ Y) || decide (e.2 ∈ Y)) := by
          rw [List.filter_filter]
          refine List.filter_congr fun e he => ?_
          have h1_lt : e.1 ∈ G_twin.verts := Finset.mem_range.mpr (hTV e he).1
          have h2_lt : e.2 ∈ G_twin.verts := Finset.mem_range.mpr (hTV e he).2
          unfold Cited.partsOf at hY_mem
          rcases Finset.mem_image.mp hY_mem with ⟨z, _, rfl⟩
          simp only [Finset.mem_filter, h1_lt, h2_lt, true_and]
          by_cases h1e : label.getD e.1 0 = label.getD z 0 <;>
            by_cases h2e : label.getD e.2 0 = label.getD z 0
          · simp only [List.getD_eq_getElem?_getD] at h1e h2e
            simp [h1e, h2e]
          · simp only [List.getD_eq_getElem?_getD] at h1e h2e
            have hne : label[z]?.getD 0 ≠ label[e.2]?.getD 0 := fun h => h2e h.symm
            simp [h1e, h2e, hne]
          · simp only [List.getD_eq_getElem?_getD] at h1e h2e
            simp [h1e, h2e]
          · simp only [List.getD_eq_getElem?_getD] at h1e h2e
            simp [h1e, h2e]
        rw [hins_eq, hsub]
        clear hsub hins_eq
        induction Lc with
        | nil => simp
        | cons e es ih =>
          rw [List.filter_cons, List.filter_cons, List.filter_cons]
          cases h1 : decide (e.1 ∈ Y) <;> cases h2 : decide (e.2 ∈ Y) <;> simp_all <;> omega
      have hfst_eq : ∀ Y : Finset ℕ, (Lc.filter fun e => decide (e.1 ∈ Y)).length =
          ((Lc.map fun (e : ℕ × ℕ) => (e.1, e.1)).filter fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y)).length := by
        intro Y
        rw [List.filter_map, List.length_map]
        congr 1; refine List.filter_congr fun e _ => ?_; simp
      have hsnd_eq : ∀ Y : Finset ℕ, (Lc.filter fun e => decide (e.2 ∈ Y)).length =
          ((Lc.map fun (e : ℕ × ℕ) => (e.2, e.2)).filter fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y)).length := by
        intro Y
        rw [List.filter_map, List.length_map]
        congr 1; refine List.filter_congr fun e _ => ?_; simp
      have hsum_add : ∀ (f g : Finset ℕ → ℕ) (xs : List (Finset ℕ)),
          (xs.map fun Y => f Y + g Y).sum = (xs.map f).sum + (xs.map g).sum := by
        intro f g xs
        induction xs with
        | nil => simp
        | cons x rest ih => simp only [List.map_cons, List.sum_cons, ih]; omega
      have h1 := hlist_sum_le (fun Y => G_twin.cut Y)
        (fun Y => (Lc.filter fun e => decide (e.1 ∈ Y)).length +
          (Lc.filter fun e => decide (e.2 ∈ Y)).length)
        parts hcut_eq
      rw [hsum_add] at h1
      have hf_le := list_filter_disjoint_edges_le parts (Lc.map fun (e : ℕ × ℕ) => (e.1, e.1)) hparts_pw
      have hs_le := list_filter_disjoint_edges_le parts (Lc.map fun (e : ℕ × ℕ) => (e.2, e.2)) hparts_pw
      simp only [List.length_map] at hf_le hs_le
      have hmap1 : (parts.map fun Y => (Lc.filter fun e => decide (e.1 ∈ Y)).length).sum ≤ crossTwin := by
        have : (parts.map fun Y => (Lc.filter fun e => decide (e.1 ∈ Y)).length) =
            parts.map fun Y => ((Lc.map fun (e : ℕ × ℕ) => (e.1, e.1)).filter
              fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y)).length :=
          List.map_congr_left fun Y _ => hfst_eq Y
        rw [this]; exact hf_le
      have hmap2 : (parts.map fun Y => (Lc.filter fun e => decide (e.2 ∈ Y)).length).sum ≤ crossTwin := by
        have : (parts.map fun Y => (Lc.filter fun e => decide (e.2 ∈ Y)).length) =
            parts.map fun Y => ((Lc.map fun (e : ℕ × ℕ) => (e.2, e.2)).filter
              fun e => decide (e.1 ∈ Y) && decide (e.2 ∈ Y)).length :=
          List.map_congr_left fun Y _ => hsnd_eq Y
        rw [this]; exact hs_le
      omega
    have hrem_31 : remG.m ≤ 31 * crossTwin := by omega
    have htw_m : G_twin.m ≤ 3 * (2 ^ i * curG.n) := by
      change (twinGraph (2 ^ i) curG).m ≤ 3 * (2 ^ i * curG.n)
      rw [twinGraph_m]
      omega
    have hcross_bound : 200 * crossTwin ≤ G_twin.m := by
      have h1 : (crossTwin : ℝ) ≤ (1 / 200 : ℝ) * (G_twin.m : ℝ) := hdecCut
      exact_mod_cast (by linarith : (200 * crossTwin : ℝ) ≤ (G_twin.m : ℝ))
    have h2pow : 2 ^ i * curG.n = 2 * (2 ^ (i - 1) * curG.n) := by
      have hpow : 2 ^ i = 2 * 2 ^ (i - 1) := by
        calc 2 ^ i = 2 ^ ((i - 1) + 1) := by congr 1; omega
          _ = 2 ^ (i - 1) * 2 := Nat.pow_succ _ _
          _ = 2 * 2 ^ (i - 1) := Nat.mul_comm _ _
      rw [hpow]; ring
    omega
  have hY_disj : (uniqLabels.map (partX curG.n ∘ Y_of)).Pairwise Disjoint := by
    rw [List.pairwise_map]
    refine huniq_nd.imp ?_
    intro L₁ L₂ hne
    apply partX_disjoint
    rw [Finset.disjoint_left]
    intro z hz1 hz2
    have h1 := (Finset.mem_filter.mp hz1).2
    have h2 := (Finset.mem_filter.mp hz2).2
    exact hne (h1.symm.trans h2)
  have hvalid_disj : validRs.Pairwise Disjoint :=
    pairwise_disjoint_filter_map R_of (partX curG.n ∘ Y_of)
      (fun R => decide (2 ≤ R.card)) uniqLabels hY_disj fun L hL_mem =>
      (hpartSpec L hL_mem).1
  have hvalid_props : ∀ R ∈ validRs,
      R ⊆ curG.verts ∧ 2 ≤ R.card ∧
      Gi.IsConductanceExpanderOn R φ_out ∧
      (∀ x ∈ R, φ_out * (2 : ℝ) ^ i ≤ (Gi.degIn R x : ℝ)) ∧
      (∀ e ∈ Gi.edges, e.1 ∈ R ↔ e.2 ∈ R) := by
    intro R hR_mem
    have hR_filt := List.mem_filter.mp hR_mem
    rcases List.mem_map.mp hR_filt.1 with ⟨L, hL_uniq, rfl⟩
    have hcardR : 2 ≤ (R_of L).card := decide_eq_true_eq.mp hR_filt.2
    have hL_sp := hpartSpec L hL_uniq
    have hR_sub_verts : R_of L ⊆ curG.verts := by
      intro x hx
      exact Finset.mem_filter.mp (hL_sp.1 hx) |>.1
    have hne_R : R_of L ≠ ∅ := Finset.Nonempty.ne_empty (Finset.card_pos.mp (by omega))
    have hR_good := hL_sp.2.1.resolve_left hne_R
    have hins_eq : Gi.inside (R_of L) = curG.inside (R_of L) := by
      simp only [Gi, Cited.Graph.inside, List.filter_filter]
      refine List.filter_congr fun e _ => ?_
      by_cases h1 : e.1 ∈ R_of L <;> by_cases h2 : e.2 ∈ R_of L <;> simp [h1, h2]
      exact List.any_eq_true.mpr ⟨R_of L, hR_mem, by simp [h1, h2]⟩
    have hdeg_eq : ∀ v, Gi.degIn (R_of L) v = curG.degIn (R_of L) v := fun v => by
      simp [Cited.Graph.degIn, hins_eq]
    have hvol_eq : ∀ S, Gi.volIn (R_of L) S = curG.volIn (R_of L) S := fun S => by
      simp [Cited.Graph.volIn, hdeg_eq]
    have hcut_eq : ∀ S, Gi.cutIn (R_of L) S = curG.cutIn (R_of L) S := fun S => by
      simp [Cited.Graph.cutIn, hins_eq]
    have hexp_Gi : Gi.IsConductanceExpanderOn (R_of L) φ_out := by
      intro S hS hSne hSneR
      rw [hvol_eq S, hvol_eq (R_of L \ S), hcut_eq S]
      exact hR_good.2.1 S hS hSne hSneR
    have hdeg_Gi : ∀ x ∈ R_of L, φ_out * (2 : ℝ) ^ i ≤ (Gi.degIn (R_of L) x : ℝ) := by
      intro x hx
      rw [hdeg_eq x]
      simpa using hR_good.2.2 x hx
    have hedges_closed : ∀ e ∈ Gi.edges, e.1 ∈ R_of L ↔ e.2 ∈ R_of L := by
      intro e he
      have hpred : pred e = true := (List.mem_filter.mp he).2
      rcases List.any_eq_true.mp hpred with ⟨R', hR'_mem, heR'⟩
      have he1' : e.1 ∈ R' := by simpa using (Bool.and_eq_true _ _ |>.mp heR').1
      have he2' : e.2 ∈ R' := by simpa using (Bool.and_eq_true _ _ |>.mp heR').2
      constructor
      · intro he1
        have heq := mem_pairwise_disjoint_eq_of_mem_inter hvalid_disj hR_mem hR'_mem e.1 he1 he1'
        rwa [heq]
      · intro he2
        have heq := mem_pairwise_disjoint_eq_of_mem_inter hvalid_disj hR_mem hR'_mem e.2 he2 he2'
        rwa [heq]
    exact ⟨hR_sub_verts, hcardR, hexp_Gi, hdeg_Gi, hedges_closed⟩
  have hedges_cov : ∀ e ∈ Gi.edges, ∃ R ∈ validRs, e.1 ∈ R ∧ e.2 ∈ R := by
    intro e he
    have hpred : pred e = true := (List.mem_filter.mp he).2
    rcases List.any_eq_true.mp hpred with ⟨R, hR_mem, heR⟩
    exact ⟨R, hR_mem, by simpa using heR⟩
  exact ⟨hGiV, hGiL, hremV, hremL, hperm, hGi_m, hrem_m, hvalid_disj, hvalid_props, hedges_cov⟩

/-! ## 5. Level Count `ℓ` and Output Length `≤ 4 + 5 · G.m` -/

lemma decompose_ell_bounds {n m : ℕ} (hn : 1 ≤ n) (_hnm : n < m) :
    let ℓ := Nat.log 2 (m / n) + 1
    1 ≤ ℓ ∧ ℓ ≤ Nat.log 2 (m + 2) + 1 ∧ m ≤ 2 ^ ℓ * n := by
  intro ℓ
  have hlog : Nat.log 2 (m / n) ≤ Nat.log 2 (m + 2) :=
    Nat.log_mono_right (le_trans (Nat.div_le_self m n) (by omega))
  have hpow : m / n < 2 ^ ℓ :=
    Nat.lt_pow_succ_log_self (by decide : 1 < 2) (m / n)
  have hmul : m ≤ 2 ^ ℓ * n := by
    have hmod : m < (m / n + 1) * n := by
      have hdm := Nat.div_add_mod m n
      have hrm := Nat.mod_lt m hn
      nlinarith
    have hpow1 : m / n + 1 ≤ 2 ^ ℓ := hpow
    nlinarith
  exact ⟨by omega, by omega, hmul⟩

lemma decompose_encode_length_le_five_mul_m {c_ℓ : ℝ} {G : Cited.Graph}
    {d_ℓ phiNum phiDen : ℕ} {level : List ℕ} {rawComps : List (ℕ × List ℕ)}
    (hlevel_len : level.length = G.m)
    (hphi_pos : 1 ≤ phiNum) (hphi_le : phiNum ≤ phiDen)
    (hsorted : rawComps.Pairwise fun a b => a.1 ≤ b.1)
    (hcomp_props : ∀ c ∈ rawComps, 1 ≤ c.1 ∧ c.1 ≤ d_ℓ ∧ c.2.Pairwise (· < ·) ∧ 2 ≤ c.2.length)
    (hprop : DecomposeProp c_ℓ G (mkDecomposeOutput d_ℓ level rawComps)
      ((phiNum : ℝ) / (phiDen : ℝ))) :
    (Decompose.encode d_ℓ phiNum phiDen level rawComps).length ≤ 4 + 5 * G.m := by
  have hmatch : rawComps.map (fun c => (c.1, c.2.toFinset)) =
      (List.range d_ℓ).flatMap fun i' =>
        ((mkDecomposeOutput d_ℓ level rawComps).comps (i' + 1)).map fun X => (i' + 1, X) :=
    (mkDecomposeOutput_rawComps_eq d_ℓ level rawComps hsorted
      fun c hc => ⟨(hcomp_props c hc).1, (hcomp_props c hc).2.1⟩).symm
  have hnodup : ∀ c ∈ rawComps, c.2.Nodup ∧ 2 ≤ c.2.length := fun c hc =>
    ⟨(hcomp_props c hc).2.2.1.imp fun h => ne_of_lt h, (hcomp_props c hc).2.2.2⟩
  have hdisj : ∀ i, 1 ≤ i → i ≤ d_ℓ →
      ((mkDecomposeOutput d_ℓ level rawComps).comps i).Pairwise Disjoint :=
    fun i hi1 hiℓ => (hprop.2.2.2 i hi1 hiℓ).1
  have hc2 : ∀ i, 1 ≤ i → i ≤ d_ℓ →
      ∀ X ∈ (mkDecomposeOutput d_ℓ level rawComps).comps i, 2 ≤ X.card :=
    fun i hi1 hiℓ X hX => (hprop.2.2.2 i hi1 hiℓ).2.1 X hX |>.2.1
  have hdeg : ∀ i, 1 ≤ i → i ≤ d_ℓ →
      ∀ X ∈ (mkDecomposeOutput d_ℓ level rawComps).comps i,
        ∀ x ∈ X, 1 ≤ ((mkDecomposeOutput d_ℓ level rawComps).graphAt G i).degIn X x := by
    intro i hi1 hiℓ X hX x hx
    have hdeg_R := (hprop.2.2.2 i hi1 hiℓ).2.1 X hX |>.2.2.2.1 x hx
    have hpos_R : (0 : ℝ) < ((phiNum : ℝ) / (phiDen : ℝ)) * (2 ^ i : ℝ) := by
      have hp1 : (0 : ℝ) < phiNum := by exact_mod_cast hphi_pos
      have hp2 : (0 : ℝ) < phiDen := by exact_mod_cast (by omega : 1 ≤ phiDen)
      positivity
    exact_mod_cast (lt_of_lt_of_le hpos_R hdeg_R)
  have hsum := decompose_rawComps_size_le hmatch hnodup hdisj hc2 hdeg
  rw [decompose_encode_length, hlevel_len]
  omega

end MinCostFlow.Expander
