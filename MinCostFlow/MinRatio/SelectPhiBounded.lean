module

public import MinCostFlow.MinRatio.SelectPhiFillMath
public import MinCostFlow.MinRatio.WireSelectSplitPotModel
public import MinCostFlow.Chain.CycleLemmas

import Mathlib.Tactic

/-!
# Walk-length bounds, open-walk lifting, and `SelectPhiBoundedAt` (`SelectPhiBounded`)

Pure mathematical helpers supporting the fixed-point fit bounds for select-heap candidate keys
and BFS forest-potential fills:

1. `walkLength_le_length_mul`: for any walk `W` with `0 ≤ w x.1 ≤ B`,
   `walkLength w W ≤ W.length * B` (without requiring edge-simplicity).
2. `abs_walkInner_forestPath_le`: for any graph `F`, `|walkInner g (F.forestPath u v)| ≤ F.m * B`
   whenever `∀ e ∈ F.E, |g e| ≤ B`.
3. `abs_walkInner_sparsifierCycle_le`: under `C.Holds`, `C.LastLevelSpans`, and
   `∀ f ∈ (C.G 0).E, |g f| ≤ M_g`, every candidate cycle at `lvl ≤ C.d` satisfies
   `|walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)| ≤
     (C.sparsifierCycle lvl e).length * ((C.G 0).n + 1) * M_g`.
4. `walkInner_potGrad_lift_open`: under `C.Holds` and `∀ k < j, SelectPotInvAt C g φ k`, any walk
   `W` from `v` to `r` in `(C.activeLSF j).F.F` lifts to a walk `W₀` from `v` to `r` in
   `C.chainTree` satisfying
   `walkInner (potGrad C g φ j) W + ∑ k ∈ Finset.range j, (φ k v - φ k r) = walkInner g W₀`.
5. `SelectPhiBoundedAt`: `∀ v ∈ (C.G k).V, |φ k v| ≤ 3 ^ k * N * M_g`, proved to be preserved
   across valid batches by `splitPot` (`splitPot_abs_le_of_batchIsValid`) and established by
   `selectPhiFill`'s postcondition (`selectPhiBoundedAt_of_phiFill`).
-/

@[expose] public section

namespace MinCostFlow.MinRatio

open MinCostFlow.Chain MinCostFlow.LSF MinCostFlow.SparseCore

/-! ## 1. General walk-length and fundamental-cycle bounds -/

/-- General upper bound on `walkLength w W` without assuming edge-simplicity:
`walkLength w W ≤ W.length * B` whenever `0 ≤ w x.1 ≤ B` for every step `x ∈ W`. -/
theorem walkLength_le_length_mul {w : ℕ → ℝ} {B : ℝ} (hB : 0 ≤ B) :
    ∀ W : List (ℕ × Bool), (∀ x ∈ W, 0 ≤ w x.1 ∧ w x.1 ≤ B) →
      walkLength w W ≤ (W.length : ℝ) * B
  | [], _ => by simp [walkLength, walkEdges]
  | x :: xs, hW => by
    have hx := hW x (List.mem_cons_self ..)
    have hxs : ∀ y ∈ xs, 0 ≤ w y.1 ∧ w y.1 ≤ B := fun y hy => hW y (List.mem_cons_of_mem _ hy)
    have ih := walkLength_le_length_mul hB xs hxs
    have hstep : walkLength w (x :: xs) ≤ w x.1 + walkLength w xs := by
      unfold walkLength
      have hsub : walkEdges xs ⊆ walkEdges (x :: xs) := by
        intro f hf
        rw [walkEdges, List.mem_toFinset, List.mem_map] at hf ⊢
        obtain ⟨y, hy, rfl⟩ := hf
        exact ⟨y, List.mem_cons_of_mem _ hy, rfl⟩
      have hterm : ∀ f ∈ walkEdges (x :: xs),
          w f * |walkFlow (x :: xs) f| ≤
            (if f = x.1 then w x.1 else 0) + w f * |walkFlow xs f| := by
        intro f hf
        have hwf_nn : 0 ≤ w f := by
          rw [walkEdges, List.mem_toFinset, List.mem_map] at hf
          obtain ⟨y, hy, rfl⟩ := hf
          exact (hW y hy).1
        have hfl : walkFlow (x :: xs) f =
            (if x.1 = f then (if x.2 then (1 : ℝ) else -1) else 0) + walkFlow xs f := by
          simp only [walkFlow, List.map_cons, List.sum_cons]
        have habs : |walkFlow (x :: xs) f| ≤ (if f = x.1 then (1 : ℝ) else 0) + |walkFlow xs f| := by
          rw [hfl]
          refine (abs_add_le _ _).trans ?_
          gcongr
          by_cases hfx : f = x.1
          · subst hfx; cases x.2 <;> simp
          · have hxf : x.1 ≠ f := Ne.symm hfx
            simp [hfx, hxf]
        calc w f * |walkFlow (x :: xs) f|
            ≤ w f * ((if f = x.1 then (1 : ℝ) else 0) + |walkFlow xs f|) :=
              mul_le_mul_of_nonneg_left habs hwf_nn
          _ = (if f = x.1 then w x.1 else 0) + w f * |walkFlow xs f| := by
              by_cases hfx : f = x.1
              · subst hfx; simp [mul_add]
              · simp [hfx]
      have hsum1 : ∑ f ∈ walkEdges (x :: xs), (if f = x.1 then w x.1 else 0) = w x.1 := by
        have hxmem : x.1 ∈ walkEdges (x :: xs) := by
          rw [walkEdges, List.mem_toFinset, List.mem_map]
          exact ⟨x, List.mem_cons_self .., rfl⟩
        rw [Finset.sum_ite_eq' (walkEdges (x :: xs)) x.1 (fun _ => w x.1), ite_eq_left hxmem]
      have hsum2 : ∑ f ∈ walkEdges (x :: xs), w f * |walkFlow xs f| =
          ∑ f ∈ walkEdges xs, w f * |walkFlow xs f| := by
        symm
        refine Finset.sum_subset hsub fun f _ hfnot => ?_
        have hzero : walkFlow xs f = 0 := by
          unfold walkFlow
          apply List.sum_eq_zero
          intro y hy
          rw [List.mem_map] at hy
          obtain ⟨z, hz, rfl⟩ := hy
          have hne : z.1 ≠ f := fun heq =>
            hfnot (by rw [walkEdges, List.mem_toFinset, List.mem_map]; exact ⟨z, hz, heq⟩)
          simp [hne]
        simp [hzero]
      calc ∑ f ∈ walkEdges (x :: xs), w f * |walkFlow (x :: xs) f|
          ≤ ∑ f ∈ walkEdges (x :: xs), ((if f = x.1 then w x.1 else 0) + w f * |walkFlow xs f|) :=
            Finset.sum_le_sum hterm
        _ = (∑ f ∈ walkEdges (x :: xs), (if f = x.1 then w x.1 else 0)) +
            (∑ f ∈ walkEdges (x :: xs), w f * |walkFlow xs f|) := Finset.sum_add_distrib
        _ = w x.1 + ∑ f ∈ walkEdges xs, w f * |walkFlow xs f| := by rw [hsum1, hsum2]
    have hlen : ((x :: xs).length : ℝ) * B = B + (xs.length : ℝ) * B := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    linarith

/-- Any forest path `F.forestPath u v` satisfies `|walkInner g (F.forestPath u v)| ≤ F.m * B`
whenever `∀ e ∈ F.E, |g e| ≤ B`. -/
theorem abs_walkInner_forestPath_le {F : MGraph} {g : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hg : ∀ e ∈ F.E, |g e| ≤ B) (u v : ℕ) :
    |walkInner g (F.forestPath u v)| ≤ (F.m : ℝ) * B := by
  classical
  by_cases hconn : F.Connected u v
  · have hP : F.IsPath u v (F.forestPath u v) := MGraph.isPath_forestPath hconn
    have hnd : ((F.forestPath u v).map Prod.fst).Nodup := LSF.isPath_nodup_edges hP
    unfold walkInner
    calc |∑ e ∈ walkEdges (F.forestPath u v), g e * walkFlow (F.forestPath u v) e|
        ≤ ∑ e ∈ walkEdges (F.forestPath u v), |g e * walkFlow (F.forestPath u v) e| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _e ∈ walkEdges (F.forestPath u v), B := by
          refine Finset.sum_le_sum fun e he => ?_
          rw [abs_mul, LSF.walkFlow_abs_of_nodup hnd e, ite_eq_left he, mul_one]
          obtain ⟨dir, hmem⟩ := LSF.mem_walkEdges_iff.mp he
          exact hg e (LSF.IsWalk_edges_mem hP.1 hmem)
      _ = ((walkEdges (F.forestPath u v)).card : ℝ) * B := by simp
      _ ≤ (F.m : ℝ) * B := by
          apply mul_le_mul_of_nonneg_right _ hB
          have hsub : walkEdges (F.forestPath u v) ⊆ F.E := fun e he => by
            obtain ⟨dir, hmem⟩ := LSF.mem_walkEdges_iff.mp he
            exact LSF.IsWalk_edges_mem hP.1 hmem
          exact_mod_cast Finset.card_le_card hsub
  · have hempty : F.forestPath u v = [] := by
      unfold MGraph.forestPath
      rw [dite_eq_right_iff]
      intro h
      exact absurd ⟨h.choose, h.choose_spec.1⟩ hconn
    rw [hempty, walkInner_nil, abs_zero]
    exact mul_nonneg (Nat.cast_nonneg _) hB

private theorem abs_walkInner_stitchAux_le {G F : MGraph} {g : ℕ → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hgG : ∀ e ∈ G.E, |g e| ≤ B) (hgF : ∀ e ∈ F.E, |g e| ≤ B)
    (target : ℕ) :
    ∀ (xs : List (ℕ × Bool)) (x : ℕ × Bool),
      x.1 ∈ G.E → (∀ y ∈ xs, y.1 ∈ G.E) →
      |walkInner g (TreeChain.stitchAux G F target x xs)| ≤
        (((x :: xs).length : ℝ)) * ((F.m : ℝ) + 1) * B
  | [], x, hxE, _ => by
    simp only [TreeChain.stitchAux, walkInner_append]
    have h1 : |walkInner g [x]| ≤ B := by
      rw [walkInner_singleton]; cases x.2 <;> simp [hgG x.1 hxE]
    have h2 : |walkInner g (F.forestPath (G.dst x) target)| ≤ (F.m : ℝ) * B :=
      abs_walkInner_forestPath_le hB hgF _ _
    have hlen : (([x] : List (ℕ × Bool)).length : ℝ) = 1 := by simp
    rw [hlen]
    calc |walkInner g [x] + walkInner g (F.forestPath (G.dst x) target)|
        ≤ |walkInner g [x]| + |walkInner g (F.forestPath (G.dst x) target)| := abs_add_le _ _
      _ ≤ B + (F.m : ℝ) * B := add_le_add h1 h2
      _ = 1 * ((F.m : ℝ) + 1) * B := by ring
  | y :: ys, x, hxE, hxs => by
    have hyE : y.1 ∈ G.E := hxs y (List.mem_cons_self ..)
    have hys : ∀ z ∈ ys, z.1 ∈ G.E := fun z hz => hxs z (List.mem_cons_of_mem _ hz)
    have ih := abs_walkInner_stitchAux_le hB hgG hgF target ys y hyE hys
    simp only [TreeChain.stitchAux, List.append_assoc, walkInner_append]
    have h1 : |walkInner g [x]| ≤ B := by
      rw [walkInner_singleton]; cases x.2 <;> simp [hgG x.1 hxE]
    have h2 : |walkInner g (F.forestPath (G.dst x) (G.src y))| ≤ (F.m : ℝ) * B :=
      abs_walkInner_forestPath_le hB hgF _ _
    have hlen : (((x :: y :: ys).length : ℝ)) = 1 + (((y :: ys).length : ℝ)) := by
      simp only [List.length_cons, Nat.cast_add, Nat.cast_one]; ring
    rw [hlen]
    calc |walkInner g [x] + (walkInner g (F.forestPath (G.dst x) (G.src y)) +
            walkInner g (TreeChain.stitchAux G F target y ys))|
        ≤ |walkInner g [x]| + |walkInner g (F.forestPath (G.dst x) (G.src y)) +
            walkInner g (TreeChain.stitchAux G F target y ys)| := abs_add_le _ _
      _ ≤ |walkInner g [x]| + (|walkInner g (F.forestPath (G.dst x) (G.src y))| +
            |walkInner g (TreeChain.stitchAux G F target y ys)|) := by
          gcongr; exact abs_add_le _ _
      _ ≤ B + ((F.m : ℝ) * B + ((y :: ys).length : ℝ) * ((F.m : ℝ) + 1) * B) := by linarith
      _ = (1 + ((y :: ys).length : ℝ)) * ((F.m : ℝ) + 1) * B := by ring

/-- Magnitude bound on the candidate cycle numerator
`walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)` via `lemma_7_12` and
`C.chainTree_isForest`. -/
theorem abs_walkInner_sparsifierCycle_le {C : TreeChain} {G : MGraph} {ℓ g : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c M_g : ℝ} (hM : 0 ≤ M_g)
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hSpan : C.LastLevelSpans)
    (hg : ∀ f ∈ (C.G 0).E, |g f| ≤ M_g)
    {lvl e : ℕ} (hlvl : lvl ≤ C.d) (he : e ∈ (C.activeCore lvl).E \ (C.activeS lvl).E) :
    |walkInner (C.chainGrad g (lvl + 1)) (C.sparsifierCycle lvl e)| ≤
      ((C.sparsifierCycle lvl e).length : ℝ) * (((C.G 0).n : ℝ) + 1) * M_g := by
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hTreeSub : (C.G 0).IsSubgraph C.chainTree := C.chainTree_isSubgraph hH hSub
  have hTreeFor : C.chainTree.IsForest := C.chainTree_isForest hH hSub
  have hTreeMn : C.chainTree.m ≤ (C.G 0).n := by
    have h1 : C.chainTree.m ≤ C.chainTree.n := forest_m_le_n hTreeFor
    simpa [TreeChain.chainTree, MGraph.n] using h1
  have hgTree : ∀ f ∈ C.chainTree.E, |g f| ≤ M_g := fun f hf => hg f (hTreeSub.2.1 hf)
  have hClosed := C.sparsifierCycle_isClosedWalk hH hSpan hlvl he
  have hEdges0 : ∀ y ∈ C.sparsifierCycle lvl e, y.1 ∈ (C.G 0).E := fun y hy => by
    have hyC : y.1 ∈ (C.activeCore lvl).E := MGraph.isWalk_edges_mem hClosed y hy
    have hyGlvl : y.1 ∈ (C.G lvl).E := (Finset.mem_sdiff.mp hyC).1
    exact C.G_E_subset_of_le hH (Nat.zero_le lvl) hlvl hyGlvl
  rw [C.lemma_7_12 hH hSpan hlvl he]
  unfold TreeChain.fundChainCycleAt TreeChain.stitchCycle
  change |walkInner g (TreeChain.stitchAux (C.G 0) C.chainTree
      ((C.G 0).src (e, true)) (e, true) (walkRev (C.activeEmb lvl e)))| ≤ _
  have hxE : (e, true).1 ∈ (C.G 0).E := hEdges0 (e, true) (List.mem_cons_self ..)
  have hxsE : ∀ y ∈ walkRev (C.activeEmb lvl e), y.1 ∈ (C.G 0).E := fun y hy =>
    hEdges0 y (List.mem_cons_of_mem _ hy)
  have hst := abs_walkInner_stitchAux_le hM hg hgTree ((C.G 0).src (e, true))
    (walkRev (C.activeEmb lvl e)) (e, true) hxE hxsE
  have hmnR : (C.chainTree.m : ℝ) + 1 ≤ ((C.G 0).n : ℝ) + 1 := by exact_mod_cast Nat.succ_le_succ hTreeMn
  have hlen_nn : (0 : ℝ) ≤ ((C.sparsifierCycle lvl e).length : ℝ) := Nat.cast_nonneg _
  calc |walkInner g (TreeChain.stitchAux (C.G 0) C.chainTree ((C.G 0).src (e, true))
          (e, true) (walkRev (C.activeEmb lvl e)))|
      ≤ ((C.sparsifierCycle lvl e).length : ℝ) * ((C.chainTree.m : ℝ) + 1) * M_g := hst
    _ ≤ ((C.sparsifierCycle lvl e).length : ℝ) * (((C.G 0).n : ℝ) + 1) * M_g := by gcongr

/-! ## 2. Open-walk lifting and `SelectPhiBoundedAt` -/

private lemma walkEdges_cons_eq (x : ℕ × Bool) (xs : List (ℕ × Bool)) :
    walkEdges (x :: xs) = insert x.1 (walkEdges xs) := by
  simp [walkEdges]

private lemma walkEdges_forestPath_sub {F : MGraph} (u v : ℕ) :
    walkEdges (F.forestPath u v) ⊆ F.E := by
  classical
  intro f hf
  by_cases hconn : F.Connected u v
  · obtain ⟨dir, hmem⟩ := LSF.mem_walkEdges_iff.mp hf
    exact LSF.IsWalk_edges_mem (MGraph.isWalk_forestPath hconn) hmem
  · have hempty : F.forestPath u v = [] := by
      unfold MGraph.forestPath
      rw [dite_eq_right_iff]
      intro h
      exact absurd ⟨h.choose, h.choose_spec.1⟩ hconn
    rw [hempty] at hf
    simp [walkEdges] at hf

/-- One-level open-walk lift from `C.activeCore m` to `C.G m`, splicing `F_m`-paths at the start,
between consecutive edges, and at the end. -/
private noncomputable def liftOpenWalk (G F : MGraph) (u r : ℕ) :
    List (ℕ × Bool) → List (ℕ × Bool)
  | [] => F.forestPath u r
  | x :: xs => F.forestPath u (G.src x) ++ [x] ++ liftOpenWalk G F (G.dst x) r xs

private theorem liftOpenWalk_spec {C : TreeChain} {G : MGraph} {ℓ g : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ : ℕ → ℕ → ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {m : ℕ} (hm : m ≤ C.d)
    (hPotm : SelectPotInvAt C g φ m) :
    ∀ (W : List (ℕ × Bool)) (u r u' r' : ℕ),
      u ∈ (C.G m).V → r ∈ (C.G m).V →
      (C.activeLSF m).F.root u = u' → (C.activeLSF m).F.root r = r' →
      (C.activeCore m).IsWalk u' r' W →
      (C.G m).IsWalk u r (liftOpenWalk (C.G m) (C.activeLSF m).F.F u r W) ∧
      walkEdges (liftOpenWalk (C.G m) (C.activeLSF m).F.F u r W) ⊆
        walkEdges W ∪ (C.activeLSF m).F.F.E ∧
      walkInner (potGrad C g φ m) (liftOpenWalk (C.G m) (C.activeLSF m).F.F u r W) =
        walkInner (potGrad C g φ (m + 1)) W + φ m u - φ m r := by
  have hLm := C.activeLSF_holds hH hm
  have hRF := hLm.2.1
  have hSubF : (C.G m).IsSubgraph (C.activeLSF m).F.F := hRF.2.2.2.2
  have hGmVal : (C.G m).IsValid := C.G_isValid hH m hm
  intro W
  induction W with
  | nil =>
    intro u r u' r' hu hr hru hrr hW
    cases hW
    have hconn : (C.activeLSF m).F.F.Connected u r := connected_of_root_eq hRF hu hr (hru.trans hrr.symm)
    have hPF := MGraph.isWalk_forestPath hconn
    refine ⟨MGraph.isWalk_of_isSubgraph hSubF hPF, ?_, ?_⟩
    · intro f hf
      exact Finset.mem_union_right _ (walkEdges_forestPath_sub u r hf)
    · simp only [liftOpenWalk, walkInner_nil, zero_add]
      exact hPotm u r hconn
  | cons x xs ih =>
    intro u r u' r' hu hr hru hrr hW
    cases hW with
    | cons hxCore hsrc hrest =>
      have hxGm : x.1 ∈ (C.G m).E := (Finset.mem_sdiff.mp hxCore).1
      have hEnds := hGmVal x.1 hxGm
      have hsrcV : (C.G m).src x ∈ (C.G m).V := by
        cases hx2 : x.2 <;> simp [MGraph.src, hx2, hEnds.1, hEnds.2]
      have hdstV : (C.G m).dst x ∈ (C.G m).V := by
        cases hx2 : x.2 <;> simp [MGraph.dst, hx2, hEnds.1, hEnds.2]
      have hsrcRoot : (C.activeLSF m).F.root ((C.G m).src x) = u' := by
        have h1 : (C.activeCore m).src x = (C.activeLSF m).F.root ((C.G m).src x) := by
          cases hx2 : x.2 <;> simp [MGraph.src, TreeChain.activeCore, coreGraph, hx2]
        rw [← h1, hsrc]
      have hdstRoot : (C.activeLSF m).F.root ((C.G m).dst x) = (C.activeCore m).dst x := by
        cases hx2 : x.2 <;> simp [MGraph.dst, TreeChain.activeCore, coreGraph, hx2]
      have hconnStart : (C.activeLSF m).F.F.Connected u ((C.G m).src x) :=
        connected_of_root_eq hRF hu hsrcV (hru.trans hsrcRoot.symm)
      have hStartW : (C.G m).IsWalk u ((C.G m).src x) ((C.activeLSF m).F.F.forestPath u ((C.G m).src x)) :=
        MGraph.isWalk_of_isSubgraph hSubF (MGraph.isWalk_forestPath hconnStart)
      have hStepW : (C.G m).IsWalk ((C.G m).src x) ((C.G m).dst x) [x] :=
        .cons hxGm rfl (.nil _)
      obtain ⟨hTailW, hTailE, hTailIn⟩ := ih ((C.G m).dst x) r ((C.activeCore m).dst x) r'
        hdstV hr hdstRoot hrr hrest
      refine ⟨?_, ?_, ?_⟩
      · simp only [liftOpenWalk]
        exact MGraph.isWalk_append (MGraph.isWalk_append hStartW hStepW) hTailW
      · intro f hf
        simp only [liftOpenWalk, walkEdges_append, Finset.mem_union] at hf
        rcases hf with (hf1 | hf2) | hf3
        · exact Finset.mem_union_right _ (walkEdges_forestPath_sub _ _ hf1)
        · have hfx : f = x.1 := by simpa [walkEdges] using hf2
          subst hfx
          exact Finset.mem_union_left _ (by rw [walkEdges_cons_eq]; exact Finset.mem_insert_self _ _)
        · rcases Finset.mem_union.mp (hTailE hf3) with h1 | h2
          · exact Finset.mem_union_left _ (by rw [walkEdges_cons_eq]; exact Finset.mem_insert_of_mem h1)
          · exact Finset.mem_union_right _ h2
      · simp only [liftOpenWalk, walkInner_append]
        rw [hPotm u ((C.G m).src x) hconnStart, hTailIn, walkInner_cons (potGrad C g φ (m + 1)) x xs]
        have hstepEq : walkInner (potGrad C g φ (m + 1)) [x] =
            walkInner (potGrad C g φ m) [x] + φ m ((C.G m).dst x) - φ m ((C.G m).src x) := by
          cases hx2 : x.2
          · simp [walkInner_singleton, potGrad, MGraph.src, MGraph.dst, hx2]; ring
          · simp [walkInner_singleton, potGrad, MGraph.src, MGraph.dst, hx2]
        rw [hstepEq]
        ring

/-- Lifting an open forest walk `W` from `v` to `r` in `(C.activeLSF j).F.F` all the way to a walk
`W₀` from `v` to `r` in `C.chainTree`:
`walkInner (potGrad C g φ j) W + ∑ k ∈ Finset.range j, (φ k v - φ k r) = walkInner g W₀`. -/
theorem walkInner_potGrad_lift_open {C : TreeChain} {G : MGraph} {ℓ g : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c : ℝ} {φ : ℕ → ℕ → ℝ}
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) {j : ℕ} (hj : j ≤ C.d)
    (hPot : ∀ k < j, SelectPotInvAt C g φ k)
    {v r : ℕ} (hv : v ∈ (C.G j).V) (hr : r ∈ (C.G j).V)
    {W : List (ℕ × Bool)} (hW : (C.activeLSF j).F.F.IsWalk v r W) :
    ∃ W₀ : List (ℕ × Bool),
      C.chainTree.IsWalk v r W₀ ∧
      walkInner (potGrad C g φ j) W + ∑ k ∈ Finset.range j, (φ k v - φ k r) = walkInner g W₀ := by
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hStep : ∀ m ≤ C.d, (∀ k < m, SelectPotInvAt C g φ k) →
      ∀ (v r : ℕ) (W : List (ℕ × Bool)),
        v ∈ (C.G m).V → r ∈ (C.G m).V → (C.G m).IsWalk v r W →
        walkEdges W ⊆ C.chainTree.E →
        ∃ W₀ : List (ℕ × Bool),
          (C.G 0).IsWalk v r W₀ ∧
          walkEdges W₀ ⊆ C.chainTree.E ∧
          walkInner (potGrad C g φ m) W + ∑ k ∈ Finset.range m, (φ k v - φ k r) =
            walkInner g W₀ := by
    intro m
    induction m with
    | zero =>
      intro _ _ v r W _ _ hWm hEsub
      exact ⟨W, hWm, hEsub, by simp [potGrad]⟩
    | succ m ih =>
      intro hm1 hPotm v r W hv hr hWm hEsub
      have hm_lt : m < C.d := by omega
      have hCoreSub := C.G_succ_isSubgraph_core hH hm_lt
      have hWCore : (C.activeCore m).IsWalk v r W := MGraph.isWalk_of_isSubgraph hCoreSub hWm
      have hLm := C.activeLSF_holds hH hm_lt.le
      have hRF := hLm.2.1
      have hvR : v ∈ (C.activeLSF m).F.R := hCoreSub.1 hv
      have hrR : r ∈ (C.activeLSF m).F.R := hCoreSub.1 hr
      have hvGm : v ∈ (C.G m).V := hRF.2.2.1 hvR
      have hrGm : r ∈ (C.G m).V := hRF.2.2.1 hrR
      have hrv : (C.activeLSF m).F.root v = v := root_eq_of_mem_R hRF hvR
      have hrr : (C.activeLSF m).F.root r = r := root_eq_of_mem_R hRF hrR
      obtain ⟨hLiftW, hLiftE, hLiftIn⟩ :=
        liftOpenWalk_spec hH hm_lt.le (hPotm m (Nat.lt_succ_self m)) W v r v r
          hvGm hrGm hrv hrr hWCore
      have hLiftChain : walkEdges (liftOpenWalk (C.G m) (C.activeLSF m).F.F v r W) ⊆
          C.chainTree.E := by
        intro f hf
        rcases Finset.mem_union.mp (hLiftE hf) with h1 | h2
        · exact hEsub h1
        · simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, Finset.mem_biUnion,
            Finset.mem_range]
          exact ⟨m, by omega, h2⟩
      obtain ⟨W₀, hW₀, hE₀, hIn₀⟩ := ih hm_lt.le (fun k hk => hPotm k (Nat.lt_succ_of_lt hk))
        v r _ hvGm hrGm hLiftW hLiftChain
      refine ⟨W₀, hW₀, hE₀, ?_⟩
      rw [Finset.sum_range_succ]
      linarith
  have hWGj : (C.G j).IsWalk v r W := MGraph.isWalk_of_isSubgraph (hSub j hj) hW
  have hWEj : walkEdges W ⊆ C.chainTree.E := fun f hf => by
    obtain ⟨dir, hmem⟩ := LSF.mem_walkEdges_iff.mp hf
    have hfFj : f ∈ (C.activeLSF j).F.F.E := LSF.IsWalk_edges_mem hW hmem
    simp only [TreeChain.chainTree, TreeChain.chainTreeEdges, Finset.mem_biUnion, Finset.mem_range]
    exact ⟨j, by omega, hfFj⟩
  obtain ⟨W₀, hW₀, hE₀, hIn₀⟩ := hStep j hj hPot v r W hv hr hWGj hWEj
  have hW₀Tree : C.chainTree.IsWalk v r W₀ := by
    have haux : ∀ (a b : ℕ) (P : List (ℕ × Bool)),
        (C.G 0).IsWalk a b P → walkEdges P ⊆ C.chainTree.E → C.chainTree.IsWalk a b P := by
      intro a b P hP hPE
      induction hP with
      | nil u => exact .nil u
      | @cons u w x rest _ hsrc _ ihP =>
        have hxE : x.1 ∈ C.chainTree.E :=
          hPE (by rw [walkEdges_cons_eq]; exact Finset.mem_insert_self _ _)
        have hrestE : walkEdges rest ⊆ C.chainTree.E := fun f hf =>
          hPE (by rw [walkEdges_cons_eq]; exact Finset.mem_insert_of_mem hf)
        exact .cons hxE hsrc (ihP hrestE)
    exact haux v r W₀ hW₀ hE₀
  exact ⟨W₀, hW₀Tree, hIn₀⟩

/-- Inductive magnitude bound on frozen potentials at level `k`:
`|φ k v| ≤ 3 ^ k * N * M_g` for every vertex `v ∈ (C.G k).V`. -/
def SelectPhiBoundedAt (C : TreeChain) (φ : ℕ → ℕ → ℝ) (N : ℕ) (M_g : ℝ) (k : ℕ) : Prop :=
  ∀ v ∈ (C.G k).V, |φ k v| ≤ (3 : ℝ) ^ k * (N : ℝ) * M_g

/-- `splitPot` across any valid batch `U` preserves any uniform bound on vertex potentials. -/
theorem splitPot_abs_le_of_batchIsValid {G : MGraph} {U : List Update} (hB : G.BatchIsValid U)
    {φj : ℕ → ℝ} {B : ℝ} (hφ : ∀ v ∈ G.V, |φj v| ≤ B) :
    ∀ v ∈ (G.applyBatch U).V, |splitPot φj (batchSplits U) v| ≤ B := by
  induction U generalizing G φj with
  | nil => exact hφ
  | cons u rest ih =>
    cases u with
    | delete e =>
      simp only [MGraph.applyBatch, batchSplits]
      exact ih hB.2 (fun v hv => hφ v (by simpa [MGraph.applyUpdate] using hv))
    | insert e a b =>
      simp only [MGraph.applyBatch, batchSplits]
      exact ih hB.2 (fun v hv => hφ v (by simpa [MGraph.applyUpdate] using hv))
    | split v v' inc =>
      simp only [MGraph.applyBatch, batchSplits, splitPot]
      have hvIn : v ∈ G.V := hB.1.1
      refine ih hB.2 fun w hw => ?_
      have hw' : w = v' ∨ w ∈ G.V := by
        simpa [MGraph.applyUpdate, Finset.mem_insert] using hw
      rcases hw' with rfl | hwG
      · rw [Function.update_self]; exact hφ v hvIn
      · by_cases hne : w = v'
        · subst hne; rw [Function.update_self]; exact hφ v hvIn
        · rw [Function.update_of_ne hne]; exact hφ w hwG

private lemma geom_two_mul_three_pow (n : ℕ) :
    ∑ k ∈ Finset.range n, (2 : ℝ) * (3 : ℝ) ^ k = (3 : ℝ) ^ n - 1 := by
  induction n with
  | zero => simp
  | succ m ihm =>
    rw [Finset.sum_range_succ, ihm, pow_succ]
    ring

/-- `SelectPhiBoundedAt` is preserved by `selectPhiFill` (via postcondition 4 of
`selectPhiFillContract`, `SelectPhiFillDefs.lean`): given `SelectPotInvAt` and
`SelectPhiBoundedAt` at all levels `k < j`, the freshly filled `φj` satisfies
`SelectPhiBoundedAt C (Function.update φ j φj) N M_g j`. -/
theorem selectPhiBoundedAt_of_phiFill {C : TreeChain} {G : MGraph} {ℓ g : ℕ → ℝ}
    {σ σ_mwu γ_ℓ γ_c M_g : ℝ} {φ : ℕ → ℕ → ℝ} {φj : ℕ → ℝ} {N j : ℕ}
    (hM : 0 ≤ M_g)
    (hH : C.Holds G ℓ σ σ_mwu γ_ℓ γ_c) (hj : j ≤ C.d)
    (hN : (C.G 0).n ≤ N)
    (hg : ∀ f ∈ (C.G 0).E, |g f| ≤ M_g)
    (hPot : ∀ k < j, SelectPotInvAt C g φ k)
    (hBd : ∀ k < j, SelectPhiBoundedAt C φ N M_g k)
    (hFill : ∀ v ∈ (C.activeLSF j).F.F.V, ∃ r ∈ (C.activeLSF j).F.F.V,
      (C.activeLSF j).F.F.Connected v r ∧
      φj v = walkInner (potGrad C g φ j) ((C.activeLSF j).F.F.forestPath v r)) :
    SelectPhiBoundedAt C (Function.update φ j φj) N M_g j := by
  have hSub := C.forestsAreSubgraphs_of_holds hH
  have hRFj := (C.activeLSF_holds hH hj).2.1
  have hTreeSub := C.chainTree_isSubgraph hH hSub
  have hTreeFor := C.chainTree_isForest hH hSub
  have hgTree : ∀ f ∈ C.chainTree.E, |g f| ≤ M_g := fun f hf => hg f (hTreeSub.2.1 hf)
  have hTreeMn : C.chainTree.m ≤ N := by
    have h1 : C.chainTree.m ≤ C.chainTree.n := forest_m_le_n hTreeFor
    have h2 : C.chainTree.n = (C.G 0).n := rfl
    omega
  intro v hv
  rw [Function.update_self]
  have hvF : v ∈ (C.activeLSF j).F.F.V := hRFj.2.1.symm ▸ hv
  obtain ⟨r, hrF, hconn, hφv⟩ := hFill v hvF
  have hr : r ∈ (C.G j).V := hRFj.2.1 ▸ hrF
  obtain ⟨W₀, hW₀Tree, hLiftEq⟩ :=
    walkInner_potGrad_lift_open hH hj hPot hv hr (MGraph.isWalk_forestPath hconn)
  have hconnTree : C.chainTree.Connected v r := ⟨W₀, hW₀Tree⟩
  have hflowEq : ∀ f, walkFlow W₀ f = walkFlow (C.chainTree.forestPath v r) f :=
    walkFlow_eq_of_isForest hTreeFor hW₀Tree (MGraph.isWalk_forestPath hconnTree)
  have hW₀_eq : walkInner g W₀ = walkInner g (C.chainTree.forestPath v r) :=
    walkInner_eq_of_walkFlow_eq g hflowEq
  have hW₀_le : |walkInner g W₀| ≤ (N : ℝ) * M_g := by
    rw [hW₀_eq]
    calc |walkInner g (C.chainTree.forestPath v r)|
        ≤ (C.chainTree.m : ℝ) * M_g := abs_walkInner_forestPath_le hM hgTree v r
      _ ≤ (N : ℝ) * M_g := mul_le_mul_of_nonneg_right (by exact_mod_cast hTreeMn) hM
  have hSumLe : |∑ k ∈ Finset.range j, (φ k v - φ k r)| ≤
      ((3 : ℝ) ^ j - 1) * (N : ℝ) * M_g := by
    calc |∑ k ∈ Finset.range j, (φ k v - φ k r)|
        ≤ ∑ k ∈ Finset.range j, |φ k v - φ k r| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ k ∈ Finset.range j, (2 * (3 : ℝ) ^ k) * ((N : ℝ) * M_g) := by
          refine Finset.sum_le_sum fun k hk => ?_
          have hkj : k < j := Finset.mem_range.mp hk
          have hvk : v ∈ (C.G k).V := C.G_V_subset_of_le hH hkj.le hj hv
          have hrk : r ∈ (C.G k).V := C.G_V_subset_of_le hH hkj.le hj hr
          have h1 := hBd k hkj v hvk
          have h2 := hBd k hkj r hrk
          calc |φ k v - φ k r| ≤ |φ k v| + |φ k r| := abs_sub _ _
            _ ≤ (3 : ℝ) ^ k * (N : ℝ) * M_g + (3 : ℝ) ^ k * (N : ℝ) * M_g := add_le_add h1 h2
            _ = (2 * (3 : ℝ) ^ k) * ((N : ℝ) * M_g) := by ring
      _ = (∑ k ∈ Finset.range j, (2 : ℝ) * (3 : ℝ) ^ k) * ((N : ℝ) * M_g) :=
          (Finset.sum_mul ..).symm
      _ = ((3 : ℝ) ^ j - 1) * (N : ℝ) * M_g := by rw [geom_two_mul_three_pow j]; ring
  have hEq : φj v = walkInner g W₀ - ∑ k ∈ Finset.range j, (φ k v - φ k r) := by
    rw [hφv]; linarith
  rw [hEq]
  calc |walkInner g W₀ - ∑ k ∈ Finset.range j, (φ k v - φ k r)|
      ≤ |walkInner g W₀| + |∑ k ∈ Finset.range j, (φ k v - φ k r)| := abs_sub _ _
    _ ≤ (N : ℝ) * M_g + ((3 : ℝ) ^ j - 1) * (N : ℝ) * M_g := add_le_add hW₀_le hSumLe
    _ = (3 : ℝ) ^ j * (N : ℝ) * M_g := by ring

end MinCostFlow.MinRatio
