module

public import MinCostFlow.LSF.HLD
import Mathlib.Data.Finset.Max

/-!
# HLD auxiliary tree and Lemma B.9 ([chen2022maximum] Appendix B.3)

This file constructs the HLD auxiliary tree `T_H = hldAuxTree T r` of a rooted tree `(T, r)` and
proves **Lemma B.9** (`lemma_B_9`, `[chen2022maximum, Lemma B.9]`):
1. The height of `T_H` is at most `(Nat.log 2 n + 1) * (Nat.log 2 n + 2)` (`O(log^2 n)`).
2. For any `R ⊆ V(T)`, `R^{↑ T_H}` (`upClosure T_H r R`) is branch-free in `(T, r)`.
3. For any nonempty `R ⊆ V(T)` and edge ordering `π`, every `u ∈ V(T)` has `root^F_u ∈ u^{↑ T_H}`
   for `F = F_T(R^{↑ T_H}, π)`.
4. For any nonempty `R₁, R₂ ⊆ V(T)`, if `R₁^{↑ T_H} ∩ u^{↑ T_H} = R₂^{↑ T_H} ∩ u^{↑ T_H}`, then
   `root^{F₁}_u = root^{F₂}_u`.
-/

@[expose] public section

namespace MinCostFlow.LSF

open MinCostFlow

/-! ## Generic rooted tree from a ranking parent map -/

/-- A rooted tree on vertex set `V` with root `r`, edge IDs `V \ {r}`, and parent map `p`. -/
def treeOfParent (V : Finset ℕ) (r : ℕ) (p : ℕ → ℕ) : MGraph :=
  { V := V, E := V.erase r, tail := id, head := p }

lemma treeOfParent_isRootedTree {V : Finset ℕ} {r : ℕ} (hr : r ∈ V)
    {p rk : ℕ → ℕ} (hp : ∀ u ∈ V.erase r, p u ∈ V ∧ rk (p u) < rk u) :
    IsRootedTree (treeOfParent V r p) r := by
  let T := treeOfParent V r p
  have hV : T.V.Nonempty := ⟨r, hr⟩
  have hvalid : T.IsValid := by
    intro e he
    have he' : e ∈ V.erase r := he
    exact ⟨(Finset.mem_erase.mp he').2, (hp e he').1⟩
  have hconn_r : ∀ n u, rk u = n → u ∈ V → T.Connected u r := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro u hn hu
      by_cases hur : u = r
      · rw [hur]; exact connected_refl T r
      · have hue : u ∈ V.erase r := Finset.mem_erase.mpr ⟨hur, hu⟩
        have hpu := hp u hue
        have h_edge : T.Connected u (p u) := by
          have heT : u ∈ T.E := hue
          exact connected_of_edge heT
        exact connected_trans h_edge (ih (rk (p u)) (hn ▸ hpu.2) (p u) rfl hpu.1)
  have hconn_all : ∀ u ∈ T.V, ∀ v ∈ T.V, T.Connected u v := by
    intro u hu v hv
    exact connected_trans (hconn_r (rk u) u rfl hu) (connected_symm (hconn_r (rk v) v rfl hv))
  have hcard : T.E.card + 1 = T.V.card := Finset.card_erase_add_one hr
  exact ⟨isForest_of_connected_card hvalid rfl hV hconn_all hcard, hr⟩

private lemma walk_true_rk_le {V : Finset ℕ} {r : ℕ} {p rk : ℕ → ℕ}
    (hp : ∀ u ∈ V.erase r, p u ∈ V ∧ rk (p u) < rk u) :
    ∀ {a b : ℕ} (P : List (ℕ × Bool)), (treeOfParent V r p).IsWalk a b P →
      (∀ x ∈ P, x.2 = true) → ∀ z ∈ (treeOfParent V r p).walkVertices a P, rk z ≤ rk a := by
  intro a b P hP htrue z hz
  induction P generalizing a with
  | nil =>
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hz
    exact hz ▸ le_rfl
  | cons x P ih =>
    rcases hP with _ | ⟨he, hsrc, hw⟩
    have hxtrue : x.2 = true := htrue x List.mem_cons_self
    rcases x with ⟨e, d⟩
    dsimp only at hxtrue
    subst hxtrue
    have heE : e ∈ V.erase r := he
    have ha_eq : a = e := hsrc.symm
    have hdst : (treeOfParent V r p).dst (e, true) = p e := rfl
    have hlt : rk (p e) < rk e := (hp e heE).2
    have hmem : z ∈ a :: (treeOfParent V r p).walkVertices ((treeOfParent V r p).dst (e, true)) P := hz
    rw [List.mem_cons] at hmem
    rcases hmem with rfl | hz'
    · exact le_rfl
    · have := ih hw (fun y hy => htrue y (List.mem_cons_of_mem _ hy)) hz'
      rw [ha_eq, hdst] at *
      omega

lemma treeOfParent_parent {V : Finset ℕ} {r : ℕ} {p rk : ℕ → ℕ}
    (hr : r ∈ V) (hp : ∀ u ∈ V.erase r, p u ∈ V ∧ rk (p u) < rk u)
    {u : ℕ} (hu : u ∈ V) (hur : u ≠ r) :
    parent (treeOfParent V r p) r u = p u ∧
      IsAncestor (treeOfParent V r p) r (p u) u ∧
      depth (treeOfParent V r p) r u = depth (treeOfParent V r p) r (p u) + 1 := by
  let T := treeOfParent V r p
  have hT := treeOfParent_isRootedTree hr hp
  have h_all_true : ∀ n w, rk w = n → w ∈ V →
      ∃ Q, T.IsPath w r Q ∧ ∀ x ∈ Q, x.2 = true := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn hw
      by_cases hwr : w = r
      · subst hwr
        exact ⟨[], ⟨.nil _, by simp [MGraph.walkVertices]⟩, by simp⟩
      · have hwE : w ∈ V.erase r := Finset.mem_erase.mpr ⟨hwr, hw⟩
        obtain ⟨hpw, hrk⟩ := hp w hwE
        obtain ⟨Q, hQ, hQt⟩ := ih (rk (p w)) (hn ▸ hrk) (p w) rfl hpw
        have hw_not_in : w ∉ T.walkVertices (p w) Q := by
          intro hm
          have hle := walk_true_rk_le hp Q hQ.1 hQt w hm
          omega
        have hdst : T.dst (w, true) = p w := rfl
        refine ⟨(w, true) :: Q, ⟨.cons hwE rfl (hdst ▸ hQ.1), ?_⟩, ?_⟩
        · change (w :: T.walkVertices (p w) Q).Nodup
          exact List.nodup_cons.mpr ⟨hw_not_in, hQ.2⟩
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx'
          · rfl
          · exact hQt x hx'
  have huE : u ∈ T.E := Finset.mem_erase.mpr ⟨hur, hu⟩
  obtain ⟨Q, hQ, hQt⟩ := h_all_true (rk (p u)) (p u) rfl (hp u huE).1
  have hu_not_in : u ∉ T.walkVertices (p u) Q := by
    intro hm
    have hle := walk_true_rk_le hp Q hQ.1 hQt u hm
    have := (hp u huE).2
    omega
  have hdst : T.dst (u, true) = p u := rfl
  have hP_ur : T.IsPath u r ((u, true) :: Q) := by
    refine ⟨.cons huE rfl (hdst ▸ hQ.1), ?_⟩
    change (u :: T.walkVertices (p u) Q).Nodup
    exact List.nodup_cons.mpr ⟨hu_not_in, hQ.2⟩
  have hEq := (forestPath_eq_of_isPath hT.isForest hP_ur).symm
  have hp_eq : parent T r u = p u := by unfold parent; rw [← hEq]; rfl
  refine ⟨hp_eq, ?_, ?_⟩
  · rw [← hp_eq]; exact isAncestor_parent hT hu hur
  · rw [← hp_eq]; exact (depth_parent hT hu hur).symm

/-! ## Balanced midpoint BST on a heavy chain tail -/

/-- Parent in a midpoint-split balanced binary tree over `L`, returning `above` at the midpoint
root of `L`. -/
def bstParentWith (above : ℕ) (L : List ℕ) (u : ℕ) : ℕ :=
  if h : L.length = 0 then above
  else
    let m := L.length / 2
    let rt := L[m]'(Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))
    if u = rt then above
    else if u ∈ L.take m then bstParentWith rt (L.take m) u
    else bstParentWith rt (L.drop (m + 1)) u
termination_by L.length
decreasing_by
  · rw [List.length_take]; exact lt_of_le_of_lt (min_le_left _ _) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))
  · rw [List.length_drop]; omega

/-- Depth of `u` inside the balanced BST over `L` (distance to the midpoint root of `L`). -/
def bstDepth (L : List ℕ) (u : ℕ) : ℕ :=
  if h : L.length = 0 then 0
  else
    let m := L.length / 2
    let rt := L[m]'(Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))
    if u = rt then 0
    else if u ∈ L.take m then 1 + bstDepth (L.take m) u
    else 1 + bstDepth (L.drop (m + 1)) u
termination_by L.length
decreasing_by
  · rw [List.length_take]; exact lt_of_le_of_lt (min_le_left _ _) (Nat.div_lt_self (Nat.pos_of_ne_zero h) (by decide))
  · rw [List.length_drop]; omega

lemma mem_take_or_drop_of_mem_ne {L : List ℕ} {m u : ℕ}
    (hm : m < L.length) (hu : u ∈ L) (hne : u ≠ L[m]) :
    u ∈ L.take m ∨ u ∈ L.drop (m + 1) := by
  have hsplit := List.take_append_drop m L
  have hdrop : L.drop m = L[m] :: L.drop (m + 1) := List.drop_eq_getElem_cons hm
  have hu' : u ∈ L.take m ++ (L[m] :: L.drop (m + 1)) := by rw [← hdrop, hsplit]; exact hu
  rw [List.mem_append, List.mem_cons] at hu'
  rcases hu' with h1 | hEq | h2
  · exact Or.inl h1
  · exact absurd hEq hne
  · exact Or.inr h2

lemma bstDepth_le_log : ∀ n (L : List ℕ) (u : ℕ), L.length = n → u ∈ L →
    bstDepth L u ≤ Nat.log 2 L.length := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro L u hn hu
    rcases Nat.eq_zero_or_pos L.length with h0 | hpos
    · rw [List.length_eq_zero_iff.mp h0] at hu; simp at hu
    · unfold bstDepth
      dsimp only
      split_ifs with h_zero heq hmem
      · exact absurd h_zero (Nat.ne_of_gt hpos)
      · exact Nat.zero_le _
      · have hlen_t : (L.take (L.length / 2)).length = L.length / 2 := by
          rw [List.length_take]; omega
        have hpos_t : 1 ≤ (L.take (L.length / 2)).length := List.length_pos_of_mem hmem
        have hn2 : 2 ≤ L.length := by omega
        have hlt : (L.take (L.length / 2)).length < n := by omega
        have hih := ih _ hlt (L.take (L.length / 2)) u rfl hmem
        rw [hlen_t] at hih
        have hlog : Nat.log 2 (L.length / 2) + 1 = Nat.log 2 L.length := by
          rw [Nat.log_div_base 2 L.length]
          have hlog_pos : 1 ≤ Nat.log 2 L.length := Nat.log_pos (by decide) hn2
          omega
        omega
      · have hm : L.length / 2 < L.length := Nat.div_lt_self hpos (by decide)
        have hdrop : u ∈ L.drop (L.length / 2 + 1) := by
          rcases mem_take_or_drop_of_mem_ne hm hu heq with h1 | h2
          · exact absurd h1 hmem
          · exact h2
        have hlen_d : (L.drop (L.length / 2 + 1)).length = L.length - (L.length / 2 + 1) :=
          List.length_drop
        have hpos_d : 1 ≤ (L.drop (L.length / 2 + 1)).length := List.length_pos_of_mem hdrop
        have hn2 : 2 ≤ L.length := by omega
        have hlt : (L.drop (L.length / 2 + 1)).length < n := by omega
        have hih := ih _ hlt (L.drop (L.length / 2 + 1)) u rfl hdrop
        have hmono : Nat.log 2 (L.drop (L.length / 2 + 1)).length ≤ Nat.log 2 (L.length / 2) :=
          Nat.log_mono_right (by omega)
        have hlog : Nat.log 2 (L.length / 2) + 1 = Nat.log 2 L.length := by
          rw [Nat.log_div_base 2 L.length]
          have hlog_pos : 1 ≤ Nat.log 2 L.length := Nat.log_pos (by decide) hn2
          omega
        omega

lemma disjoint_take_drop_nodup {L : List ℕ} (hnd : L.Nodup) (m : ℕ) :
    (∀ x ∈ L.take m, ∀ hm : m < L.length, x ≠ L[m]) ∧
    (∀ x ∈ L.drop (m + 1), ∀ hm : m < L.length, x ≠ L[m]) ∧
    (∀ x ∈ L.take m, x ∉ L.drop (m + 1)) := by
  by_cases hm : m < L.length
  · have hsplit := List.take_append_drop m L
    have hdrop : L.drop m = L[m] :: L.drop (m + 1) := List.drop_eq_getElem_cons hm
    have hnd' : (L.take m ++ L[m] :: L.drop (m + 1)).Nodup := by rwa [← hdrop, hsplit]
    rw [List.nodup_append, List.nodup_cons] at hnd'
    refine ⟨fun x hx _ hEq => ?_, fun x hx _ hEq => ?_, fun x hx h2 => ?_⟩
    · exact hnd'.2.2 x hx (L[m]) List.mem_cons_self hEq
    · exact hnd'.2.1.1 (hEq ▸ hx)
    · exact hnd'.2.2 x hx x (List.mem_cons_of_mem _ h2) rfl
  · refine ⟨fun _ _ hm' => absurd hm' hm, fun _ _ hm' => absurd hm' hm, fun _ _ h2 => ?_⟩
    have hnil : L.drop (m + 1) = [] := List.drop_eq_nil_iff.mpr (by omega)
    rw [hnil] at h2
    simp at h2

lemma bstParentWith_spec : ∀ n (above : ℕ) (L : List ℕ) (u : ℕ) (hu : u ∈ L),
    L.length = n → L.Nodup →
      (u = L[L.length / 2]'(Nat.div_lt_self (List.length_pos_of_mem hu) (by decide)) →
          bstParentWith above L u = above ∧ bstDepth L u = 0) ∧
      (u ≠ L[L.length / 2]'(Nat.div_lt_self (List.length_pos_of_mem hu) (by decide)) →
          bstParentWith above L u ∈ L ∧
          bstDepth L (bstParentWith above L u) + 1 = bstDepth L u) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro above L u hu hn hnd
    have hpos : 0 < L.length := List.length_pos_of_mem hu
    have hm : L.length / 2 < L.length := Nat.div_lt_self hpos (by decide)
    obtain ⟨h_t_ne, h_d_ne, h_td⟩ := disjoint_take_drop_nodup hnd (L.length / 2)
    constructor
    · intro heq
      constructor
      · conv_lhs => unfold bstParentWith; dsimp only
        rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos))]
        exact ite_eq_left_iff.mpr (fun hne' => absurd heq hne')
      · conv_lhs => unfold bstDepth; dsimp only
        rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos))]
        exact ite_eq_left_iff.mpr (fun hne' => absurd heq hne')
    · intro hne
      have hsub_t : L.take (L.length / 2) ⊆ L := List.take_subset _ _
      have hsub_d : L.drop (L.length / 2 + 1) ⊆ L := List.drop_subset _ _
      rcases mem_take_or_drop_of_mem_ne hm hu hne with hu_t | hu_d
      · have hpar_eq : bstParentWith above L u =
            bstParentWith (L[L.length / 2]) (L.take (L.length / 2)) u := by
          conv_lhs => unfold bstParentWith; dsimp only
          rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos)),
              ite_eq_right_iff.mpr (fun h => absurd h hne),
              ite_eq_left_iff.mpr (fun h => absurd hu_t h)]
        have hd_eq : bstDepth L u = 1 + bstDepth (L.take (L.length / 2)) u := by
          conv_lhs => unfold bstDepth; dsimp only
          rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos)),
              ite_eq_right_iff.mpr (fun h => absurd h hne),
              ite_eq_left_iff.mpr (fun h => absurd hu_t h)]
        have hlen_t : (L.take (L.length / 2)).length < n := by
          rw [List.length_take]; omega
        have hpos_t := List.length_pos_of_mem hu_t
        have hm_t : (L.take (L.length / 2)).length / 2 < (L.take (L.length / 2)).length :=
          Nat.div_lt_self hpos_t (by decide)
        obtain ⟨ih_eq, ih_ne⟩ := ih _ hlen_t (L[L.length / 2]) (L.take (L.length / 2)) u hu_t rfl
          hnd.take
        rw [hpar_eq, hd_eq]
        by_cases hu_rt : u = (L.take (L.length / 2))[(L.take (L.length / 2)).length / 2]
        · obtain ⟨hp', hd'⟩ := ih_eq hu_rt
          rw [hp', hd']
          refine ⟨List.getElem_mem hm, ?_⟩
          have hd_rt : bstDepth L (L[L.length / 2]) = 0 := by
            conv_lhs => unfold bstDepth; dsimp only
            rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos))]
            exact ite_eq_left_iff.mpr (fun h => absurd rfl h)
          omega
        · obtain ⟨hp_mem, hd'⟩ := ih_ne hu_rt
          have hp_in_L := hsub_t hp_mem
          have hp_ne : bstParentWith (L[L.length / 2]) (L.take (L.length / 2)) u ≠ L[L.length / 2] :=
            h_t_ne _ hp_mem hm
          have hdp : bstDepth L (bstParentWith (L[L.length / 2]) (L.take (L.length / 2)) u) =
              1 + bstDepth (L.take (L.length / 2)) (bstParentWith (L[L.length / 2]) (L.take (L.length / 2)) u) := by
            conv_lhs => unfold bstDepth; dsimp only
            rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos)),
                ite_eq_right_iff.mpr (fun h => absurd h hp_ne),
                ite_eq_left_iff.mpr (fun h => absurd hp_mem h)]
          rw [hdp]
          exact ⟨hp_in_L, by omega⟩
      · have hu_not_t : u ∉ L.take (L.length / 2) := fun hm' => h_td u hm' hu_d
        have hpar_eq : bstParentWith above L u =
            bstParentWith (L[L.length / 2]) (L.drop (L.length / 2 + 1)) u := by
          conv_lhs => unfold bstParentWith; dsimp only
          rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos)),
              ite_eq_right_iff.mpr (fun h => absurd h hne),
              ite_eq_right_iff.mpr (fun h => absurd h hu_not_t)]
        have hd_eq : bstDepth L u = 1 + bstDepth (L.drop (L.length / 2 + 1)) u := by
          conv_lhs => unfold bstDepth; dsimp only
          rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos)),
              ite_eq_right_iff.mpr (fun h => absurd h hne),
              ite_eq_right_iff.mpr (fun h => absurd h hu_not_t)]
        have hlen_d : (L.drop (L.length / 2 + 1)).length < n := by
          rw [List.length_drop]; omega
        have hpos_d := List.length_pos_of_mem hu_d
        obtain ⟨ih_eq, ih_ne⟩ := ih _ hlen_d (L[L.length / 2]) (L.drop (L.length / 2 + 1)) u hu_d rfl
          hnd.drop
        rw [hpar_eq, hd_eq]
        by_cases hu_rt : u = (L.drop (L.length / 2 + 1))[(L.drop (L.length / 2 + 1)).length / 2]
        · obtain ⟨hp', hd'⟩ := ih_eq hu_rt
          rw [hp', hd']
          refine ⟨List.getElem_mem hm, ?_⟩
          have hd_rt : bstDepth L (L[L.length / 2]) = 0 := by
            conv_lhs => unfold bstDepth; dsimp only
            rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos))]
            exact ite_eq_left_iff.mpr (fun h => absurd rfl h)
          omega
        · obtain ⟨hp_mem, hd'⟩ := ih_ne hu_rt
          have hp_in_L := hsub_d hp_mem
          have hp_ne : bstParentWith (L[L.length / 2]) (L.drop (L.length / 2 + 1)) u ≠ L[L.length / 2] :=
            h_d_ne _ hp_mem hm
          have hp_not_t : bstParentWith (L[L.length / 2]) (L.drop (L.length / 2 + 1)) u ∉ L.take (L.length / 2) :=
            fun hm' => h_td _ hm' hp_mem
          have hdp : bstDepth L (bstParentWith (L[L.length / 2]) (L.drop (L.length / 2 + 1)) u) =
              1 + bstDepth (L.drop (L.length / 2 + 1)) (bstParentWith (L[L.length / 2]) (L.drop (L.length / 2 + 1)) u) := by
            conv_lhs => unfold bstDepth; dsimp only
            rw [dite_eq_right_of_eq_false (eq_false (Nat.ne_of_gt hpos)),
                ite_eq_right_iff.mpr (fun h => absurd h hp_ne),
                ite_eq_right_iff.mpr (fun h => absurd h hp_not_t)]
          rw [hdp]
          exact ⟨hp_in_L, by omega⟩

/-! ## HLD auxiliary tree `T_H` -/

/-- The upward closure `R^{↑ TH} = ⋃_{u ∈ R} u^{↑ TH}` in a rooted tree `(TH, r)`. -/
noncomputable def upClosure (TH : MGraph) (r : ℕ) (R : Finset ℕ) : Finset ℕ :=
  R.biUnion (ancestors TH r)

lemma mem_upClosure_iff {TH : MGraph} {r : ℕ} {R : Finset ℕ} {w : ℕ} :
    w ∈ upClosure TH r R ↔ ∃ u ∈ R, IsAncestor TH r w u := by
  simp only [upClosure, Finset.mem_biUnion, mem_ancestors_iff]

lemma upClosure_subset {TH : MGraph} {r : ℕ} (hTH : IsRootedTree TH r)
    {R : Finset ℕ} (hR : R ⊆ TH.V) : upClosure TH r R ⊆ TH.V := by
  intro w hw
  rw [mem_upClosure_iff] at hw
  obtain ⟨u, hu, hwu⟩ := hw
  exact isAncestor_mem hTH (hR hu) hwu

lemma subset_upClosure {TH : MGraph} {r : ℕ} {R : Finset ℕ} : R ⊆ upClosure TH r R := by
  intro u hu
  rw [mem_upClosure_iff]
  exact ⟨u, hu, isAncestor_refl TH r u⟩

lemma upClosure_isUpwardClosed {TH : MGraph} {r : ℕ} (hTH : IsRootedTree TH r)
    {R : Finset ℕ} (hR : R ⊆ TH.V) {w z : ℕ}
    (hw : w ∈ upClosure TH r R) (hz : IsAncestor TH r z w) :
    z ∈ upClosure TH r R := by
  rw [mem_upClosure_iff] at hw ⊢
  obtain ⟨u, hu, hwu⟩ := hw
  exact ⟨u, hu, isAncestor_trans hTH (hR hu) hz hwu⟩

lemma upClosure_upClosure {TH : MGraph} {r : ℕ} (hTH : IsRootedTree TH r)
    {R : Finset ℕ} (hR : R ⊆ TH.V) :
    upClosure TH r (upClosure TH r R) = upClosure TH r R := by
  apply Finset.Subset.antisymm _ subset_upClosure
  intro z hz
  rw [mem_upClosure_iff] at hz
  obtain ⟨w, hw, hzw⟩ := hz
  exact upClosure_isUpwardClosed hTH hR hw hzw

/-- The heavy chain of `T` containing `u`. -/
noncomputable def chainOf (T : MGraph) (r u : ℕ) : Finset ℕ :=
  compOf (heavyGraph T r) u

lemma chainOf_mem_heavyChains {T : MGraph} {r u : ℕ} (hu : u ∈ T.V) :
    chainOf T r u ∈ heavyChains T r :=
  compOf_mem_components (G := heavyGraph T r) hu

lemma mem_chainOf_self {T : MGraph} {r u : ℕ} (hu : u ∈ T.V) :
    u ∈ chainOf T r u :=
  self_mem_compOf (G := heavyGraph T r) hu

lemma chainOf_eq_of_mem {T : MGraph} {r u : ℕ} {C : Finset ℕ}
    (hC : C ∈ heavyChains T r) (hu : u ∈ C) : chainOf T r u = C := by
  rw [heavyChains, components, Finset.mem_image] at hC
  obtain ⟨v, _, rfl⟩ := hC
  have hu' := mem_compOf_iff.mp hu
  exact ((compOf_eq_iff (G := heavyGraph T r) hu'.1).mpr hu'.2).symm

/-- Parent map for the HLD auxiliary tree `T_H` of `(T, r)`. -/
noncomputable def thParent (T : MGraph) (r u : ℕ) : ℕ :=
  let C := chainOf T r u
  let t := chainTop T r C
  let L := (chainList T r C).tail
  if u = t then parent T r t else bstParentWith t L u

/-- Strictly decreasing rank function for `thParent` (chain top depth * `(n + 1)` + BST depth). -/
noncomputable def thRank (T : MGraph) (r u : ℕ) : ℕ :=
  let C := chainOf T r u
  let t := chainTop T r C
  let L := (chainList T r C).tail
  depth T r t * (T.V.card + 1) + (if u = t then 0 else 1 + bstDepth L u)

/-- The HLD auxiliary tree `T_H` (`[chen2022maximum, Lemma B.9]`). -/
noncomputable def hldAuxTree (T : MGraph) (r : ℕ) : MGraph :=
  treeOfParent T.V r (thParent T r)

lemma chainList_tail_mem_iff {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    {P : Finset ℕ} (hP : P ∈ heavyChains T r) {u : ℕ} :
    u ∈ (chainList T r P).tail ↔ u ∈ P ∧ u ≠ chainTop T r P := by
  obtain ⟨_, tail, hEq⟩ := chainList_strictSorted_depth hT hP
  have hnd := chainList_nodup hT hP
  rw [hEq, List.nodup_cons] at hnd
  rw [hEq, List.tail_cons]
  constructor
  · intro hu
    have huP : u ∈ P := (mem_chainList_iff hT hP).mp (by rw [hEq]; exact List.mem_cons_of_mem _ hu)
    exact ⟨huP, fun h => hnd.1 (h ▸ hu)⟩
  · rintro ⟨huP, hne⟩
    have huL := (mem_chainList_iff hT hP).mpr huP
    rw [hEq, List.mem_cons] at huL
    rcases huL with rfl | hu'
    · exact absurd rfl hne
    · exact hu'

lemma thParent_rank_spec {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    ∀ u ∈ T.V.erase r, thParent T r u ∈ T.V ∧ thRank T r (thParent T r u) < thRank T r u := by
  intro u hu
  rw [Finset.mem_erase] at hu
  rcases hu with ⟨hur, huV⟩
  let C := chainOf T r u
  have hC : C ∈ heavyChains T r := chainOf_mem_heavyChains huV
  have huC : u ∈ C := mem_chainOf_self huV
  let t := chainTop T r C
  have htC : t ∈ C := (chainTop_spec hT hC).1
  have htV : t ∈ T.V := (heavyChain_subset hC).2 htC
  let L := (chainList T r C).tail
  have hnd_L : L.Nodup := (chainList_nodup hT hC).tail
  have hL_sub : ∀ x ∈ L, x ∈ C := fun x hx => ((chainList_tail_mem_iff hT hC).mp hx).1
  have hL_len_lt : L.length < T.V.card := by
    have hnd := chainList_nodup hT hC
    have hcard_L : L.toFinset.card ≤ T.V.card := by
      apply Finset.card_le_card
      intro x hx
      rw [List.mem_toFinset] at hx
      exact (heavyChain_subset hC).2 (hL_sub x hx)
    have hL_len_eq : L.length = L.toFinset.card := (List.toFinset_card_of_nodup hnd_L).symm
    obtain ⟨_, tail, hEq⟩ := chainList_strictSorted_depth hT hC
    have ht_not_L : t ∉ L := fun hm => ((chainList_tail_mem_iff hT hC).mp hm).2 rfl
    have hlt_card : L.toFinset.card < T.V.card := by
      have hss : L.toFinset ⊂ T.V := by
        rw [Finset.ssubset_iff_of_subset (fun x hx => (heavyChain_subset hC).2 (hL_sub x (List.mem_toFinset.mp hx)))]
        exact ⟨t, htV, by rw [List.mem_toFinset]; exact ht_not_L⟩
      exact Finset.card_lt_card hss
    omega
  by_cases hut : u = t
  · have htr : t ≠ r := hut ▸ hur
    have hp_mem := parent_mem hT htV
    have hpar_eq : thParent T r u = parent T r t := by
      unfold thParent
      exact ite_eq_left_iff.mpr (fun h => absurd hut h)
    rw [hpar_eq]
    refine ⟨hp_mem, ?_⟩
    have hC' : chainOf T r (parent T r t) ∈ heavyChains T r := chainOf_mem_heavyChains hp_mem
    have hp_in_C' : parent T r t ∈ chainOf T r (parent T r t) := mem_chainOf_self hp_mem
    have ht'_mem := (chainTop_spec hT hC').1
    have ht'_anc := (chainTop_spec hT hC').2 _ hp_in_C'
    have hdt' : depth T r (chainTop T r (chainOf T r (parent T r t))) ≤ depth T r (parent T r t) :=
      isAncestor_depth_le hT hp_mem ht'_anc
    have hdp := depth_parent hT htV htr
    have hoff_bound : (if parent T r t = chainTop T r (chainOf T r (parent T r t)) then 0
        else 1 + bstDepth (chainList T r (chainOf T r (parent T r t))).tail (parent T r t)) ≤ T.V.card := by
      split_ifs with hpt
      · omega
      · have hp_in_L' : parent T r t ∈ (chainList T r (chainOf T r (parent T r t))).tail :=
          (chainList_tail_mem_iff hT hC').mpr ⟨hp_in_C', hpt⟩
        have hbd := bstDepth_le_log _ _ _ rfl hp_in_L'
        have hlen' : (chainList T r (chainOf T r (parent T r t))).tail.length < T.V.card := by
          have hnd' := (chainList_nodup hT hC').tail
          have hss : (chainList T r (chainOf T r (parent T r t))).tail.toFinset ⊂ T.V := by
            rw [Finset.ssubset_iff_of_subset (fun x hx =>
              (heavyChain_subset hC').2 ((chainList_tail_mem_iff hT hC').mp (List.mem_toFinset.mp hx)).1)]
            exact ⟨chainTop T r (chainOf T r (parent T r t)),
              (heavyChain_subset hC').2 ht'_mem,
              by rw [List.mem_toFinset]; exact fun hm => ((chainList_tail_mem_iff hT hC').mp hm).2 rfl⟩
          rw [← List.toFinset_card_of_nodup hnd']
          exact Finset.card_lt_card hss
        have hlog_le : Nat.log 2 (chainList T r (chainOf T r (parent T r t))).tail.length ≤
            (chainList T r (chainOf T r (parent T r t))).tail.length := Nat.log_le_self _ _
        omega
    unfold thRank
    change depth T r (chainTop T r (chainOf T r (parent T r t))) * (T.V.card + 1) +
        (if parent T r t = chainTop T r (chainOf T r (parent T r t)) then 0
         else 1 + bstDepth (chainList T r (chainOf T r (parent T r t))).tail (parent T r t)) <
      depth T r t * (T.V.card + 1) + (if u = t then 0 else 1 + bstDepth L u)
    rw [ite_eq_left_iff.mpr (fun h => absurd hut h)]
    have hm_le : depth T r (chainTop T r (chainOf T r (parent T r t))) * (T.V.card + 1) + (T.V.card + 1) ≤
        depth T r t * (T.V.card + 1) := by
      have : depth T r (chainTop T r (chainOf T r (parent T r t))) + 1 ≤ depth T r t := by omega
      calc depth T r (chainTop T r (chainOf T r (parent T r t))) * (T.V.card + 1) + (T.V.card + 1)
          = (depth T r (chainTop T r (chainOf T r (parent T r t))) + 1) * (T.V.card + 1) := by
            rw [Nat.add_mul, Nat.one_mul]
        _ ≤ depth T r t * (T.V.card + 1) := Nat.mul_le_mul_right _ this
    omega
  · have huL : u ∈ L := (chainList_tail_mem_iff hT hC).mpr ⟨huC, hut⟩
    have hpos_L := List.length_pos_of_mem huL
    have hm : L.length / 2 < L.length := Nat.div_lt_self hpos_L (by decide)
    obtain ⟨ih_eq, ih_ne⟩ := bstParentWith_spec L.length t L u huL rfl hnd_L
    have hpar_eq : thParent T r u = bstParentWith t L u := by
      unfold thParent
      exact ite_eq_right_iff.mpr (fun h => absurd h hut)
    rw [hpar_eq]
    by_cases hurt : u = L[L.length / 2]
    · obtain ⟨hp_eq, _⟩ := ih_eq hurt
      rw [hp_eq]
      refine ⟨htV, ?_⟩
      unfold thRank
      change depth T r (chainTop T r (chainOf T r t)) * (T.V.card + 1) +
          (if t = chainTop T r (chainOf T r t) then 0 else 1 + bstDepth _ t) <
        depth T r t * (T.V.card + 1) + (if u = t then 0 else 1 + bstDepth L u)
      have hCeq : chainOf T r t = C :=
        ((compOf_eq_iff (G := heavyGraph T r) htV).mpr (mem_compOf_iff.mp htC).2).symm
      rw [hCeq]
      change depth T r t * (T.V.card + 1) + (if t = t then 0 else 1 + bstDepth _ t) <
        depth T r t * (T.V.card + 1) + (if u = t then 0 else 1 + bstDepth L u)
      rw [ite_eq_left_iff.mpr (fun h => absurd rfl h),
          ite_eq_right_iff.mpr (fun h => absurd h hut)]
      omega
    · obtain ⟨hp_in_L, hd_lt⟩ := ih_ne hurt
      have hpC : bstParentWith t L u ∈ C := hL_sub _ hp_in_L
      have hpV : bstParentWith t L u ∈ T.V := (heavyChain_subset hC).2 hpC
      refine ⟨hpV, ?_⟩
      have hCeq : chainOf T r (bstParentWith t L u) = C :=
        ((compOf_eq_iff (G := heavyGraph T r) hpV).mpr (mem_compOf_iff.mp hpC).2).symm
      have hp_ne_t : bstParentWith t L u ≠ t := ((chainList_tail_mem_iff hT hC).mp hp_in_L).2
      unfold thRank
      change depth T r (chainTop T r (chainOf T r (bstParentWith t L u))) * (T.V.card + 1) +
          (if bstParentWith t L u = chainTop T r (chainOf T r (bstParentWith t L u)) then 0
           else 1 + bstDepth (chainList T r (chainOf T r (bstParentWith t L u))).tail (bstParentWith t L u)) <
        depth T r t * (T.V.card + 1) + (if u = t then 0 else 1 + bstDepth L u)
      rw [hCeq]
      change depth T r t * (T.V.card + 1) + (if bstParentWith t L u = t then 0 else 1 + bstDepth L _) <
        depth T r t * (T.V.card + 1) + (if u = t then 0 else 1 + bstDepth L u)
      rw [ite_eq_right_iff.mpr (fun h => absurd h hp_ne_t),
          ite_eq_right_iff.mpr (fun h => absurd h hut)]
      omega

lemma hldAuxTree_isRootedTree {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    IsRootedTree (hldAuxTree T r) r :=
  treeOfParent_isRootedTree hT.2 (thParent_rank_spec hT)

lemma hldAuxTree_parent {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hur : u ≠ r) :
    parent (hldAuxTree T r) r u = thParent T r u ∧
      IsAncestor (hldAuxTree T r) r (thParent T r u) u ∧
      depth (hldAuxTree T r) r u = depth (hldAuxTree T r) r (thParent T r u) + 1 :=
  treeOfParent_parent hT.2 (thParent_rank_spec hT) hu hur

/-! ## Height of `T_H` (Condition 1) -/

private lemma thDepth_chain_le {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    ∀ k C u, C ∈ heavyChains T r → u ∈ (chainList T r C).tail →
      bstDepth (chainList T r C).tail u = k →
      depth (hldAuxTree T r) r u ≤ depth (hldAuxTree T r) r (chainTop T r C) + 1 + k := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro C u hC huL hdk
    have huC : u ∈ C := ((chainList_tail_mem_iff hT hC).mp huL).1
    have hut : u ≠ chainTop T r C := ((chainList_tail_mem_iff hT hC).mp huL).2
    have huV : u ∈ T.V := (heavyChain_subset hC).2 huC
    have htr : u ≠ r := by
      intro hEq
      rw [hEq] at huC
      have ht_anc := (chainTop_spec hT hC).2 r huC
      exact hut (hEq.trans (isAncestor_antisymm hT hT.2 ((heavyChain_subset hC).2 (chainTop_spec hT hC).1)
        (isAncestor_root hT ((heavyChain_subset hC).2 (chainTop_spec hT hC).1)) ht_anc))
    have hnd_L := (chainList_nodup hT hC).tail
    obtain ⟨ih_eq, ih_ne⟩ := bstParentWith_spec (chainList T r C).tail.length (chainTop T r C) _ u huL rfl hnd_L
    have hCeq : chainOf T r u = C := chainOf_eq_of_mem hC huC
    have hpar_eq : parent (hldAuxTree T r) r u =
        bstParentWith (chainTop T r C) (chainList T r C).tail u := by
      rw [(hldAuxTree_parent hT huV htr).1]
      unfold thParent
      rw [hCeq]
      exact ite_eq_right_iff.mpr (fun h => absurd h hut)
    have hdp := (hldAuxTree_parent hT huV htr).2.2
    rw [← (hldAuxTree_parent hT huV htr).1] at hdp
    by_cases hurt : u = (chainList T r C).tail[(chainList T r C).tail.length / 2]'(
        Nat.div_lt_self (List.length_pos_of_mem huL) (by decide))
    · obtain ⟨hp_eq, _⟩ := ih_eq hurt
      rw [hpar_eq, hp_eq] at hdp
      omega
    · obtain ⟨hpL, hdp_bst⟩ := ih_ne hurt
      have hlt : bstDepth (chainList T r C).tail
          (bstParentWith (chainTop T r C) (chainList T r C).tail u) < k := by omega
      have hih := ih _ hlt C _ hC hpL rfl
      rw [hpar_eq] at hdp
      omega

private lemma thDepth_chainTop_le {T : MGraph} {r : ℕ} (hT : IsRootedTree T r) :
    ∀ k t, (lightAncestors T r t).card = k → t ∈ T.V → t = chainTop T r (chainOf T r t) →
      depth (hldAuxTree T r) r t ≤ k * (Nat.log 2 T.V.card + 2) := by
  intro k
  induction k using Nat.strong_induction_on with
  | h k ih =>
    intro t hk htV htop
    by_cases htr : t = r
    · have h_r : depth (hldAuxTree T r) r r = 0 := by
        unfold depth
        rw [forestPath_self (hldAuxTree_isRootedTree hT).isForest r, List.length_nil]
      rw [htr, h_r]
      exact Nat.zero_le _
    · have hC : chainOf T r t ∈ heavyChains T r := chainOf_mem_heavyChains htV
      have hnot_heavy : ¬ IsHeavyChild T r t := htop ▸ chainTop_not_heavy hT hC (htop ▸ htr)
      have hp_mem := parent_mem hT htV
      have hC' : chainOf T r (parent T r t) ∈ heavyChains T r := chainOf_mem_heavyChains hp_mem
      have hp_in_C' : parent T r t ∈ chainOf T r (parent T r t) := mem_chainOf_self hp_mem
      have ht'_mem := (chainTop_spec hT hC').1
      have ht'_V : chainTop T r (chainOf T r (parent T r t)) ∈ T.V := (heavyChain_subset hC').2 ht'_mem
      have ht'_anc_p : IsAncestor T r (chainTop T r (chainOf T r (parent T r t))) (parent T r t) :=
        (chainTop_spec hT hC').2 _ hp_in_C'
      have ht'_anc_t : IsAncestor T r (chainTop T r (chainOf T r (parent T r t))) t :=
        isAncestor_trans hT htV ht'_anc_p (isAncestor_parent hT htV htr)
      have hsub_la : lightAncestors T r (chainTop T r (chainOf T r (parent T r t))) ⊆
          (lightAncestors T r t).erase t := by
        classical
        intro w hw
        rw [Finset.mem_erase]
        rw [lightAncestors, Finset.mem_filter, mem_ancestors_iff] at hw
        refine ⟨fun hEq => ?_, Finset.mem_filter.mpr ⟨mem_ancestors_iff.mpr
          (isAncestor_trans hT htV hw.1 ht'_anc_t), hw.2⟩⟩
        rw [hEq] at hw
        have hd1 := isAncestor_depth_le hT hp_mem (isAncestor_trans hT hp_mem hw.1 ht'_anc_p)
        have hd2 := depth_parent hT htV htr
        omega
      have ht_in_la : t ∈ lightAncestors T r t := by
        classical
        exact Finset.mem_filter.mpr ⟨mem_ancestors_iff.mpr (isAncestor_refl T r t), htr, hnot_heavy⟩
      have hcard_lt : (lightAncestors T r (chainTop T r (chainOf T r (parent T r t)))).card < k := by
        have hle := Finset.card_le_card hsub_la
        have hc := Finset.card_erase_add_one ht_in_la
        omega
      have ht'_top : chainTop T r (chainOf T r (parent T r t)) =
          chainTop T r (chainOf T r (chainTop T r (chainOf T r (parent T r t)))) :=
        congrArg (chainTop T r) (chainOf_eq_of_mem hC' ht'_mem).symm
      have hih := ih _ hcard_lt (chainTop T r (chainOf T r (parent T r t))) rfl ht'_V ht'_top
      have hdp_TH : depth (hldAuxTree T r) r t = depth (hldAuxTree T r) r (parent T r t) + 1 := by
        have := (hldAuxTree_parent hT htV htr).2.2
        have hpar : thParent T r t = parent T r t := by
          unfold thParent
          rw [ite_eq_left_iff.mpr (fun h => absurd htop h), ← htop]
        rwa [hpar] at this
      have hp_depth_bound : depth (hldAuxTree T r) r (parent T r t) ≤
          depth (hldAuxTree T r) r (chainTop T r (chainOf T r (parent T r t))) + 1 + Nat.log 2 T.V.card := by
        by_cases hpt' : parent T r t = chainTop T r (chainOf T r (parent T r t))
        · conv_lhs => rw [hpt']
          omega
        · have hp_in_L' : parent T r t ∈ (chainList T r (chainOf T r (parent T r t))).tail :=
            (chainList_tail_mem_iff hT hC').mpr ⟨hp_in_C', hpt'⟩
          have h1 := thDepth_chain_le hT _ (chainOf T r (parent T r t)) (parent T r t) hC' hp_in_L' rfl
          have h2 := bstDepth_le_log _ _ _ rfl hp_in_L'
          have hlen : (chainList T r (chainOf T r (parent T r t))).tail.length ≤ T.V.card := by
            have hnd := (chainList_nodup hT hC').tail
            rw [← List.toFinset_card_of_nodup hnd]
            exact Finset.card_le_card (fun x hx => (heavyChain_subset hC').2
              ((chainList_tail_mem_iff hT hC').mp (List.mem_toFinset.mp hx)).1)
          have hlog_mono := Nat.log_mono_right (b := 2) hlen
          omega
      have hmul : (lightAncestors T r (chainTop T r (chainOf T r (parent T r t)))).card *
            (Nat.log 2 T.V.card + 2) + (Nat.log 2 T.V.card + 2) ≤
          k * (Nat.log 2 T.V.card + 2) := by
        calc (lightAncestors T r (chainTop T r (chainOf T r (parent T r t)))).card *
              (Nat.log 2 T.V.card + 2) + (Nat.log 2 T.V.card + 2)
            = ((lightAncestors T r (chainTop T r (chainOf T r (parent T r t)))).card + 1) *
                (Nat.log 2 T.V.card + 2) := by rw [Nat.add_mul, Nat.one_mul]
          _ ≤ k * (Nat.log 2 T.V.card + 2) := Nat.mul_le_mul_right _ (by omega)
      omega

lemma hldAuxTree_height {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r) (hu : u ∈ T.V) :
    depth (hldAuxTree T r) r u ≤ (Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) := by
  have hC : chainOf T r u ∈ heavyChains T r := chainOf_mem_heavyChains hu
  have huC : u ∈ chainOf T r u := mem_chainOf_self hu
  have htC : chainTop T r (chainOf T r u) ∈ chainOf T r u := (chainTop_spec hT hC).1
  have htV : chainTop T r (chainOf T r u) ∈ T.V := (heavyChain_subset hC).2 htC
  have ht_top : chainTop T r (chainOf T r u) =
      chainTop T r (chainOf T r (chainTop T r (chainOf T r u))) :=
    congrArg (chainTop T r) (chainOf_eq_of_mem hC htC).symm
  have ht_depth := thDepth_chainTop_le hT _ _ rfl htV ht_top
  have hlog_t := lightAncestors_card_le hT htV
  have ht_mul : (lightAncestors T r (chainTop T r (chainOf T r u))).card * (Nat.log 2 T.V.card + 2) ≤
      Nat.log 2 T.V.card * (Nat.log 2 T.V.card + 2) := Nat.mul_le_mul_right _ hlog_t
  by_cases hut : u = chainTop T r (chainOf T r u)
  · rw [hut]
    calc depth (hldAuxTree T r) r (chainTop T r (chainOf T r u))
        ≤ (lightAncestors T r (chainTop T r (chainOf T r u))).card *
            (Nat.log 2 T.V.card + 2) := ht_depth
      _ ≤ Nat.log 2 T.V.card * (Nat.log 2 T.V.card + 2) := ht_mul
      _ ≤ (Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) :=
        Nat.mul_le_mul_right _ (Nat.le_succ _)
  · have huL : u ∈ (chainList T r (chainOf T r u)).tail :=
      (chainList_tail_mem_iff hT hC).mpr ⟨huC, hut⟩
    have h1 := thDepth_chain_le hT _ (chainOf T r u) u hC huL rfl
    have h2 := bstDepth_le_log _ _ _ rfl huL
    have hlen : (chainList T r (chainOf T r u)).tail.length ≤ T.V.card := by
      have hnd := (chainList_nodup hT hC).tail
      rw [← List.toFinset_card_of_nodup hnd]
      exact Finset.card_le_card (fun x hx => (heavyChain_subset hC).2
        ((chainList_tail_mem_iff hT hC).mp (List.mem_toFinset.mp hx)).1)
    have hlog_mono := Nat.log_mono_right (b := 2) hlen
    have hadd : Nat.log 2 T.V.card * (Nat.log 2 T.V.card + 2) + (Nat.log 2 T.V.card + 2) =
        (Nat.log 2 T.V.card + 1) * (Nat.log 2 T.V.card + 2) := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

end MinCostFlow.LSF
