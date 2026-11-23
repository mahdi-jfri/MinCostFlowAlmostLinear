module

public import MinCostFlow.LinkCut.PathTree.NumForest
public import MinCostFlow.LinkCut.PathTree.Acc
import MinCostFlow.LinkCut.ForestReversals
import MinCostFlow.LinkCut.ForestModelOps

/-!
# The numbers of an expose fit

An expose is a splay and a detach, a loop of splices, and a last splay. Each splice is a splay
of the path parent, a detach, and an attach. `NumForest` shows that each of these keeps the
forest bounds `ForestB` and that its numbers fit. This file chains them:

* `exposeStep_num`: one splice;
* `exposeLoop_num`: the loop, by induction on the fuel;
* `expose_num`: the whole expose (`ExposeOk`), and the bounds after it.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathTree

open MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.SplayState
  MinCostFlow.LinkCut.Gen MinCostFlow.LinkCut.Path

/-- A node of the forest is in a chosen tree or in the rest. -/
theorem mem_flatMap_erase {trees : List AuxTree} {t : AuxTree} (ht : t ∈ trees) {z : ℕ}
    (hz : z ∈ trees.flatMap AuxTree.toList) :
    z ∈ t.toList ∨ z ∈ (trees.erase t).flatMap AuxTree.toList := by
  have hp := (List.perm_cons_erase ht).flatMap_right AuxTree.toList
  have := hp.mem_iff.mp hz
  rw [List.flatMap_cons, List.mem_append] at this
  exact this

theorem active_splay {trees : List AuxTree} {t t' : AuxTree} (ht : t ∈ trees)
    (hperm : t'.toList.Perm t.toList) {z : ℕ} (hz : z ∈ trees.flatMap AuxTree.toList) :
    z ∈ (t' :: trees.erase t).flatMap AuxTree.toList := by
  rw [List.flatMap_cons, List.mem_append]
  rcases mem_flatMap_erase ht hz with h | h
  · exact Or.inl (hperm.mem_iff.mpr h)
  · exact Or.inr h

theorem active_detach {trees : List AuxTree} {x : ℕ} {L Rt : AuxTree}
    (ht : AuxTree.node x L Rt ∈ trees) {z : ℕ} (hz : z ∈ trees.flatMap AuxTree.toList) :
    z ∈ (if Rt = .leaf then trees else
      AuxTree.node x L .leaf :: Rt :: trees.erase (.node x L Rt)).flatMap AuxTree.toList := by
  by_cases hRl : Rt = .leaf
  · simpa [hRl] using hz
  simp only [hRl, ↓reduceIte, List.flatMap_cons, List.mem_append]
  rcases mem_flatMap_erase ht hz with h | h
  · simp only [AuxTree.toList, List.mem_append, List.mem_singleton, List.not_mem_nil,
      or_false] at h ⊢
    tauto
  · exact Or.inr (Or.inr h)

theorem active_attach {trees : List AuxTree} {u : ℕ} {Lu tx : AuxTree}
    (htu : AuxTree.node u Lu .leaf ∈ trees) (htx : tx ∈ trees)
    (hne : AuxTree.node u Lu .leaf ≠ tx) {z : ℕ} (hz : z ∈ trees.flatMap AuxTree.toList) :
    z ∈ (AuxTree.node u Lu tx :: ((trees.erase (.node u Lu .leaf)).erase tx)).flatMap
      AuxTree.toList := by
  rw [List.flatMap_cons, List.mem_append]
  rcases mem_flatMap_erase htu hz with h | h
  · left
    simp only [AuxTree.toList, List.mem_append, List.mem_singleton, List.not_mem_nil,
      or_false] at h ⊢
    tauto
  · rcases mem_flatMap_erase ((List.mem_erase_of_ne hne.symm).mpr htx) h with h | h
    · left; simp [AuxTree.toList, h]
    · exact Or.inr h

/-- One splice of the expose loop. -/
theorem exposeStep_num {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R)
    {t_prev : AuxTree} (ht_prev : t_prev ∈ trees)
    (hp_nz : (st.splay.nodes t_prev.rootId).ppar ≠ 0) :
    let p := (st.splay.nodes t_prev.rootId).ppar
    (SplayOk (pathOk h K) pathPayload st.splay (2 * st.n + 1) p ∧
      DetachRightOk (pathOk h K) pathPayload (splay pathPayload st.splay (2 * st.n + 1) p) p ∧
      AttachRightOk (pathOk h K) pathPayload
        (detachRight pathPayload (splay pathPayload st.splay (2 * st.n + 1) p) p) p
        t_prev.rootId) ∧
    ∃ trees', LctInvWith pathPayload (lctExposeStep pathPayload st t_prev.rootId).1 trees' fl d ∧
      ForestB (lctExposeStep pathPayload st t_prev.rootId).1 trees' V R ∧
      (∃ t ∈ trees', t.rootId = p) ∧
      ∀ z ∈ trees.flatMap AuxTree.toList, z ∈ trees'.flatMap AuxTree.toList := by
  intro p
  set last := t_prev.rootId with ht_rt
  set active := trees.flatMap AuxTree.toList with hactive
  set par0 := inducedSubPar pathPayload st.splay trees with hpar0
  have hp_act : p ∈ active := W.pparActive t_prev ht_prev hp_nz
  rcases List.mem_flatMap.mp hp_act with ⟨tp, htp, hp_tp⟩
  let h_prev := listHead0 (treeIds pathPayload st.splay t_prev)
  have hh_mem : h_prev ∈ t_prev.toList := listHead0_mem_of_ne_nil (W.treesNonEmpty t_prev ht_prev)
  have hh_act : h_prev ∈ active := List.mem_flatMap.mpr ⟨t_prev, ht_prev, hh_mem⟩
  have hpar_h : par0 h_prev = p := by
    rw [hpar0, inducedSubPar_eq_of_mem (P := pathPayload) (s := st.splay) W.activeNodup ht_prev
      hh_mem]
    have hne : treeIds pathPayload st.splay t_prev ≠ [] :=
      treeIds_ne_nil (W.treesNonEmpty t_prev ht_prev)
    cases hids : treeIds pathPayload st.splay t_prev with
    | nil => exact absurd hids hne
    | cons a rest => simp [h_prev, listHead0, hids, chainPred, p]
  have htp_ne : tp ≠ t_prev := by
    intro heq
    have hp_prev : p ∈ t_prev.toList := heq ▸ hp_tp
    have hrc := tree_reaches_head W ht_prev hp_prev
    have hle := depth_le_of_reaches (fun _ hx hp => W.subPar_mem_active hx hp) W.acyclic
      active.length h_prev p hrc hp_act
    have hlt := W.acyclic h_prev hh_act (by rw [← hpar0, hpar_h]; exact hp_nz)
    rw [← hpar0, hpar_h] at hlt
    omega
  have hdisj : ∀ w ∈ t_prev.toList, w ∉ tp.toList := fun w hw hm =>
    htp_ne (flatMap_mem_unique W.activeNodup htp ht_prev hm hw)
  obtain ⟨hsOk, tp', htp'_ne, htp'_rt, htp'_perm, -, hrev_p, htag_p, hW1, hB1, hout1⟩ :=
    splay_num W hB C htp hp_tp
  cases htp'_eq : tp' with
  | leaf => exact absurd htp'_eq htp'_ne
  | node pr L Rr =>
    have hpr : pr = p := by simpa [htp'_eq, AuxTree.rootId] using htp'_rt
    rw [htp'_eq, hpr] at hW1 hB1
    rw [htp'_eq, hpr] at htp'_perm
    set s1 := splay pathPayload st.splay (2 * st.n + 1) p with hs1
    set trees1 := AuxTree.node p L Rr :: trees.erase tp with htrees1
    have hmem1 : AuxTree.node p L Rr ∈ trees1 := List.mem_cons_self
    have hprev1 : t_prev ∈ trees1 :=
      List.mem_cons_of_mem _ ((List.mem_erase_of_ne htp_ne.symm).mpr ht_prev)
    have hT1 := hW1.treesInv _ hmem1
    obtain ⟨-, hrev2, htag2, -, -, -, -, hout2⟩ :=
      detachRight_preserves pathPayload_laws hT1 hrev_p htag_p
    obtain ⟨hdOk, hW2, hB2⟩ := detach_num hW1 hB1 C hmem1 hrev_p htag_p
    have hne_prev : AuxTree.node p L Rr ≠ t_prev := by
      intro h
      have : p ∈ t_prev.toList := h ▸ (by simp [AuxTree.toList])
      exact hdisj p this hp_tp
    have hL2 : AuxTree.node p L .leaf ∈ (if Rr = .leaf then trees1 else
        AuxTree.node p L .leaf :: Rr :: trees1.erase (.node p L Rr)) := by
      by_cases hRl : Rr = .leaf
      · simp only [hRl, ↓reduceIte]; rw [← hRl]; exact hmem1
      · simp [hRl]
    have hprev2 : t_prev ∈ (if Rr = .leaf then trees1 else
        AuxTree.node p L .leaf :: Rr :: trees1.erase (.node p L Rr)) := by
      by_cases hRl : Rr = .leaf
      · simpa [hRl] using hprev1
      · simp only [hRl, ↓reduceIte]
        exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          ((List.mem_erase_of_ne hne_prev.symm).mpr hprev1))
    have hne2 : AuxTree.node p L .leaf ≠ t_prev := by
      intro h
      have : p ∈ t_prev.toList := h ▸ (by simp [AuxTree.toList])
      exact hdisj p this hp_tp
    have hlast_out : last ∉ (AuxTree.node p L Rr).toList := by
      intro h
      exact hdisj last (AuxTree.rootId_mem (W.treesNonEmpty _ ht_prev))
        (htp'_perm.mem_iff.mp h)
    have hpp2 : ((detachRight pathPayload s1 p).nodes last).ppar = p := by
      rw [hout2 last hlast_out, hout1 last (fun h => hlast_out (htp'_perm.mem_iff.mpr h))]
    obtain ⟨haOk, hW3, hB3⟩ := attach_num hW2 hB2 C hL2 hprev2 hne2 hrev2 htag2 hpp2
    refine ⟨⟨hsOk, hdOk, haOk⟩, _, hW3, hB3, ⟨_, List.mem_cons_self, rfl⟩, fun z hz => ?_⟩
    have h1 : z ∈ trees1.flatMap AuxTree.toList := active_splay htp htp'_perm hz
    exact active_attach hL2 hprev2 hne2 (active_detach hmem1 h1)

/-- The loop of splices. -/
theorem exposeLoop_num {h K : ℕ} {V R : ℤ} :
    ∀ (fuel : ℕ) {st : PathTreeState} {trees : List AuxTree} {fl : List ℕ} {d : ℕ → ℕ}
      {t_last : AuxTree}, LctInvWith pathPayload st trees fl d → ForestB st trees V R →
      NumCtx h K (2 * st.n + 1) V R → t_last ∈ trees →
      ExposeLoopOk (pathOk h K) pathPayload st fuel t_last.rootId ∧
      ∃ trees', LctInvWith pathPayload (lctExposeLoop pathPayload st fuel t_last.rootId).1
          trees' fl d ∧
        ForestB (lctExposeLoop pathPayload st fuel t_last.rootId).1 trees' V R ∧
        ∀ z ∈ trees.flatMap AuxTree.toList, z ∈ trees'.flatMap AuxTree.toList
  | 0, _, trees, _, _, _, W, hB, _, _ => ⟨trivial, trees, W, hB, fun _ h => h⟩
  | fuel + 1, st, trees, fl, d, t_last, W, hB, C, ht => by
    by_cases hp : (st.splay.nodes t_last.rootId).ppar = 0
    · refine ⟨fun h => absurd hp h, ?_⟩
      have : lctExposeLoop pathPayload st (fuel + 1) t_last.rootId =
          (st, t_last.rootId, 0, 0) := by
        simp [lctExposeLoop, hp]
      rw [this]
      exact ⟨trees, W, hB, fun _ h => h⟩
    obtain ⟨⟨h1, h2, h3⟩, trees', W', hB', ⟨t', ht', hrt'⟩, hact⟩ := exposeStep_num W hB C ht hp
    have ih := exposeLoop_num fuel W' hB' C ht'
    rw [hrt'] at ih
    have hloop : (lctExposeLoop pathPayload st (fuel + 1) t_last.rootId).1 =
        (lctExposeLoop pathPayload (lctExposeStep pathPayload st t_last.rootId).1 fuel
          (st.splay.nodes t_last.rootId).ppar).1 := by
      rw [lctExposeLoop]
      simp only [beq_iff_eq, hp, ↓reduceIte]
      rfl
    refine ⟨fun _ => ⟨h1, h2, h3, ih.1⟩, ?_⟩
    rw [hloop]
    obtain ⟨trees'', W'', hB'', hact'⟩ := ih.2
    exact ⟨trees'', W'', hB'', fun z hz => hact' z (hact z hz)⟩

/-- A whole expose: its numbers fit, and the forest keeps its bounds. -/
theorem expose_num {h K : ℕ} {V R : ℤ} {st : PathTreeState} {trees : List AuxTree}
    {fl : List ℕ} {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d)
    (hB : ForestB st trees V R) (C : NumCtx h K (2 * st.n + 1) V R) {v : ℕ}
    (hv : v ∈ trees.flatMap AuxTree.toList) :
    ExposeOk (pathOk h K) pathPayload st v ∧
    ∃ trees', LctInvWith pathPayload (lctExpose pathPayload st v) trees' fl d ∧
      ForestB (lctExpose pathPayload st v) trees' V R ∧
      ∀ z ∈ trees.flatMap AuxTree.toList, z ∈ trees'.flatMap AuxTree.toList := by
  obtain ⟨tv, htv, hvt⟩ := List.mem_flatMap.mp hv
  obtain ⟨hs0, t', hne, hrt, hperm, -, hrev, htag, hW1, hB1, -⟩ := splay_num W hB C htv hvt
  cases ht'_eq : t' with
  | leaf => exact absurd ht'_eq hne
  | node v' L Rr =>
    have hv' : v' = v := by simpa [ht'_eq, AuxTree.rootId] using hrt
    rw [ht'_eq, hv'] at hW1 hB1 hperm
    set trees1 := AuxTree.node v L Rr :: trees.erase tv with htrees1
    have hmem1 : AuxTree.node v L Rr ∈ trees1 := List.mem_cons_self
    obtain ⟨hdOk, hW2, hB2⟩ := detach_num hW1 hB1 C hmem1 hrev htag
    have hL2 : AuxTree.node v L .leaf ∈ (if Rr = .leaf then trees1 else
        AuxTree.node v L .leaf :: Rr :: trees1.erase (.node v L Rr)) := by
      by_cases hRl : Rr = .leaf
      · simp only [hRl, ↓reduceIte]; rw [← hRl]; exact hmem1
      · simp [hRl]
    have hv2 := active_detach hmem1 (active_splay htv hperm hv)
    obtain ⟨hlOk, trees3, hW3, hB3, hact3⟩ := exposeLoop_num (2 * st.n + 1) hW2 hB2 C hL2
    set st3 := (lctExposeLoop pathPayload (exposeStart pathPayload st v) (2 * st.n + 1) v).1
      with hst3
    have hn3 : st3.n = st.n := lctExposeLoop_n pathPayload _ _ _
    have C3 : NumCtx h K (2 * st3.n + 1) V R := by rw [hn3]; exact C
    obtain ⟨t3, ht3, hv3⟩ := List.mem_flatMap.mp (hact3 v hv2)
    obtain ⟨hs4, t4, -, -, hperm4, -, -, -, hW4, hB4, -⟩ := splay_num hW3 hB3 C3 ht3 hv3
    have hs4' : SplayOk (pathOk h K) pathPayload st3.splay (2 * st3.n + 1) v := hs4
    rw [hn3] at hs4'
    have hEq : lctExpose pathPayload st v =
        (⟨st3.n, splay pathPayload st3.splay (2 * st3.n + 1) v, st3.freeHead⟩ :
          PathTreeState) := by
      rw [hn3]; rfl
    refine ⟨⟨hs0, hdOk, hlOk, ?_⟩, ?_⟩
    · exact hs4'
    · rw [hEq]
      refine ⟨_, hW4, hB4, fun z hz => ?_⟩
      exact active_splay ht3 hperm4 (hact3 z (active_detach hmem1 (active_splay htv hperm hz)))

end MinCostFlow.LinkCut.PathTree
