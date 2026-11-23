module

public import MinCostFlow.MinRatio.SolverRep
public import MinCostFlow.MinRatio.UpdateGoodApplyPaths
import MinCostFlow.MinRatio.PathFlowBookkeeping
import MinCostFlow.MinRatio.TreeEditAccountDirection
import MinCostFlow.LSF.Walks
import MinCostFlow.Chain.WalkFlow

/-!
# Exact tree-path flow and detector accounting for `lctPathApply` and `applyPathsFold`

Connects the link-cut path operation `lctPathApply pathPayload s (vid u) (vid v) (PathTag.ofFlow mult)`
and its fold `applyPathsFold` to `F.forestPath u v` on the active tree `F = chainTree`:
1. `treeEditNamedSlots_connected`: `F.Connected u v → pathTreeConnected s (vid u) (vid v)`.
2. `parentWalk_forestPath`: when `s` is rooted at `vid u` (`par (vid u) = 0`), the edge slots
   reaching `vid v` in `inducedSubPar` are precisely `walkEdges (F.forestPath u v)`, and their
   parent-child orientation matches the signed traversal direction of `F.forestPath u v`.
3. `lctPathApply_step_account` & `applyPathsFold_account`: applying `PathTag.ofFlow mult` along
   `paths` preserves `TreeEditNamedSlots` and `SolverEdgeOrientInv`, and updates every tree edge's
   `originalFlow` and `detector` by the exact signed and absolute path sums over `paths`.
-/

public section

namespace MinCostFlow.MinRatio

open LinkCut Chain

/-- Under `TreeEditNamedSlots`, graph connectivity in `F` implies `pathTreeConnected` in `s`. -/
theorem treeEditNamedSlots_connected {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {F : MGraph} {slot name : ℕ → ℕ} {u v : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hn : TreeEditNamedSlots s trees F slot name)
    (hV : ∀ e ∈ F.E, F.tail e < s.n ∧ F.head e < s.n)
    (hu : u < s.n) (hv : v < s.n) (hconn : F.Connected u v) :
    pathTreeConnected s (vid u) (vid v) := by
  rw [pathTreeConnected_iff_induced_roots hi hu hv]
  let par := inducedSubPar pathPayload s.splay trees
  let N := (trees.flatMap AuxTree.toList).length
  have hedge : ∀ e ∈ F.E, subRoot par N (vid (F.tail e)) = subRoot par N (vid (F.head e)) := by
    intro e he
    obtain ⟨htLt, hhLt⟩ := hV e he
    have hta : vid (F.tail e) ∈ trees.flatMap AuxTree.toList := hi.verticesActive _ htLt
    have hha : vid (F.head e) ∈ trees.flatMap AuxTree.toList := hi.verticesActive _ hhLt
    have hsa : slot e ∈ trees.flatMap AuxTree.toList := (hn.forward e he).1
    have hsNZ : slot e ≠ 0 := by have := (hn.forward e he).2.1.1; omega
    have htNZ : vid (F.tail e) ≠ 0 := by unfold vid; omega
    have hhNZ : vid (F.head e) ≠ 0 := by unfold vid; omega
    rcases hn.endpoints e he with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have s1 := subRoot_step_eq hi hta (h1.symm ▸ hsNZ)
      have s2 := subRoot_step_eq hi hsa (h2.symm ▸ hhNZ)
      rw [h1] at s1; rw [h2] at s2; exact s1.trans s2
    · have s1 := subRoot_step_eq hi hha (h1.symm ▸ hsNZ)
      have s2 := subRoot_step_eq hi hsa (h2.symm ▸ htNZ)
      rw [h1] at s1; rw [h2] at s2; exact (s1.trans s2).symm
  obtain ⟨walk, hwalk⟩ := hconn
  clear hu hv
  induction hwalk with
  | nil _ => rfl
  | @cons a b x rest he hsrc _ ih =>
    have hstep : subRoot par N (vid a) = subRoot par N (vid (F.dst x)) := by
      cases hx : x.2
      · simp only [MGraph.src, hx, Bool.false_eq_true, ↓reduceIte] at hsrc
        simp only [MGraph.dst, hx, Bool.false_eq_true, ↓reduceIte]
        rw [← hsrc]; exact (hedge x.1 he).symm
      · simp only [MGraph.src, hx, ↓reduceIte] at hsrc
        simp only [MGraph.dst, hx, ↓reduceIte]
        rw [← hsrc]; exact hedge x.1 he
    exact hstep.trans ih

private theorem reaches_of_zero_eq {par : ℕ → ℕ} {k z u : ℕ}
    (h0 : par u = 0) (hr : reaches par k z u = true) : z = u := by
  cases k with
  | zero => exact (by simpa [reaches] using hr : u = z).symm
  | succ k =>
    by_cases hzu : u = z
    · exact hzu.symm
    · simp [reaches, hzu, h0] at hr

private theorem depth_le_of_reaches_aux {active : List ℕ} {par depth : ℕ → ℕ}
    (hmem : ∀ x ∈ active, par x ≠ 0 → par x ∈ active)
    (hdec : ∀ x ∈ active, par x ≠ 0 → depth (par x) < depth x) :
    ∀ k u x, x ∈ active → reaches par k u x = true → depth u ≤ depth x := by
  intro k
  induction k with
  | zero =>
    intro u x _ h
    have hEq : x = u := by simpa [reaches] using h
    rw [hEq]
  | succ k ih =>
    intro u x hx h
    by_cases hxu : x = u
    · rw [hxu]
    · by_cases hp : par x = 0
      · simp [reaches, hxu, hp] at h
      · have hr : reaches par k u (par x) = true := by simpa [reaches, hxu, hp] using h
        exact le_trans (ih u (par x) (hmem x hx hp) hr) (le_of_lt (hdec x hx hp))

private theorem child_ne_parent_aux {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {slot child : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hsa : slot ∈ trees.flatMap AuxTree.toList) (hca : child ∈ trees.flatMap AuxTree.toList)
    (hslot : isEdgeSlot s.n slot) (hchild : inducedSubPar pathPayload s.splay trees child = slot) :
    child ≠ inducedSubPar pathPayload s.splay trees slot := by
  intro hEq
  have hsNZ : slot ≠ 0 := by have := hslot.1; omega
  have hpNZ : inducedSubPar pathPayload s.splay trees slot ≠ 0 := (hi.edgeParVertex slot hsa hslot).1
  have d1 := hi.acyclic child hca (hchild.symm ▸ hsNZ)
  have d2 := hi.acyclic slot hsa hpNZ
  rw [hchild] at d1
  rw [← hEq] at d2
  omega

private theorem walkVertices_append_single {G : MGraph} {u w v : ℕ} {P : List (ℕ × Bool)}
    {x : ℕ × Bool} (hP : G.IsWalk u w P) (hx : G.IsWalk w v [x]) :
    G.walkVertices u (P ++ [x]) = G.walkVertices u P ++ [v] := by
  induction hP with
  | nil _ =>
    cases hx with
    | cons _ _ hrest => cases hrest; simp [MGraph.walkVertices]
  | cons _ _ _ ih =>
    simp only [List.cons_append, MGraph.walkVertices, List.cons.injEq, true_and]
    exact ih hx

private theorem walkFlow_of_isPath_mem {F : MGraph} {u v : ℕ} {walk : List (ℕ × Bool)}
    (hpath : F.IsPath u v walk) {x : ℕ × Bool} (hx : x ∈ walk) :
    walkFlow walk x.1 = if x.2 then 1 else -1 := by
  have hnd : (walk.map Prod.fst).Nodup := LSF.isPath_nodup_edges hpath
  clear hpath
  induction walk with
  | nil => cases hx
  | cons y rest ih =>
    simp only [List.map_cons, List.nodup_cons] at hnd
    simp only [List.mem_cons] at hx
    rcases hx with rfl | hx
    · have hnot : x.1 ∉ walkEdges rest := by
        simp only [walkEdges, List.mem_toFinset]; exact hnd.1
      rw [walkFlow_cons, walkFlow_eq_zero_of_not_mem hnot, add_zero]
      simp
    · have hne : y.1 ≠ x.1 := fun h => hnd.1 (h ▸ List.mem_map_of_mem hx)
      rw [walkFlow_cons, ih hx hnd.2]
      simp [hne]

/-- Walking up `inducedSubPar` from `vid v` to root `vid u` recovers `F.forestPath u v`:
the edge slots reaching `vid v` are exactly `walkEdges (F.forestPath u v)`, and each edge's
parent-child direction matches its orientation in `F.forestPath u v`. -/
theorem parentWalk_forestPath {s : PathTreeState} {trees : List AuxTree}
    {free : List ℕ} {depth : ℕ → ℕ} {F : MGraph} {slot name : ℕ → ℕ} {u v : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hn : TreeEditNamedSlots s trees F slot name)
    (hF : F.IsForest)
    (hV : ∀ e ∈ F.E, F.tail e < s.n ∧ F.head e < s.n ∧ F.tail e ≠ F.head e)
    (hu : u < s.n) (hv : v < s.n)
    (hpar0 : inducedSubPar pathPayload s.splay trees (vid u) = 0)
    (hreach : reaches (inducedSubPar pathPayload s.splay trees)
      (trees.flatMap AuxTree.toList).length (vid u) (vid v) = true) :
    let par := inducedSubPar pathPayload s.splay trees
    let N := (trees.flatMap AuxTree.toList).length
    (∀ e ∈ F.E, reaches par N (slot e) (vid v) = true ↔ e ∈ walkEdges (F.forestPath u v)) ∧
    (∀ e ∈ F.E, e ∈ walkEdges (F.forestPath u v) →
      (par (vid (F.head e)) = slot e ∧ par (slot e) = vid (F.tail e) →
        walkFlow (F.forestPath u v) e = 1) ∧
      (par (vid (F.tail e)) = slot e ∧ par (slot e) = vid (F.head e) →
        walkFlow (F.forestPath u v) e = -1)) := by
  let par := inducedSubPar pathPayload s.splay trees
  let active := trees.flatMap AuxTree.toList
  let N := active.length
  have hmem_sub : ∀ z ∈ active, par z ≠ 0 → par z ∈ active := fun z hz hp => hi.subPar_mem_active hz hp
  have hstep_iff : ∀ {a x}, x ∈ active →
      (reaches par N a x = true ↔ x = a ∨ (par x ≠ 0 ∧ reaches par N a (par x) = true)) :=
    fun hx => reaches_step_iff hi.activeNodup hmem_sub hi.acyclic hx
  have hslot_inj : ∀ e₁ ∈ F.E, ∀ e₂ ∈ F.E, slot e₁ = slot e₂ → e₁ = e₂ := fun e₁ h1 e₂ h2 h => by
    have n1 := (hn.forward e₁ h1).2.2
    have n2 := (hn.forward e₂ h2).2.2
    rw [h] at n1; exact n1.symm.trans n2
  have haux : ∀ k w, w < s.n → reaches par k (vid u) (vid w) = true →
      ∃ walk : List (ℕ × Bool),
        F.IsPath u w walk ∧
        (∀ z ∈ F.walkVertices u walk, reaches par N (vid z) (vid w) = true) ∧
        (∀ e ∈ F.E, reaches par N (slot e) (vid w) = true ↔ e ∈ walkEdges walk) ∧
        (∀ x ∈ walk,
          (x.2 = true → par (vid (F.head x.1)) = slot x.1 ∧ par (slot x.1) = vid (F.tail x.1)) ∧
          (x.2 = false → par (vid (F.tail x.1)) = slot x.1 ∧ par (slot x.1) = vid (F.head x.1))) := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro w hw hrk
      by_cases hwu : w = u
      · subst w
        refine ⟨[], ⟨.nil u, by simp [MGraph.walkVertices]⟩, fun z hz => ?_, fun e he => ?_, fun _ h => by cases h⟩
        · simp [MGraph.walkVertices] at hz; rw [hz]; exact reaches_self par N (vid u)
        · constructor
          · intro hr
            have hEq := reaches_of_zero_eq hpar0 hr
            exact absurd ⟨by unfold isVertex vid; omega, hEq ▸ (hn.forward e he).2.1⟩ not_vertex_and_edge
          · intro hm; simp [walkEdges] at hm
      · have hneV : vid w ≠ vid u := fun h => hwu (by unfold vid at h; omega)
        have hkPos : ∃ k1, k = k1 + 1 := by
          cases k with
          | zero => exact absurd (by simpa [reaches] using hrk : vid w = vid u) hneV
          | succ k1 => exact ⟨k1, rfl⟩
        obtain ⟨k1, rfl⟩ := hkPos
        have hp1NZ : par (vid w) ≠ 0 := by
          intro h0; simp [reaches, hneV, h0] at hrk
        have hr1 : reaches par k1 (vid u) (par (vid w)) = true := by
          simpa [reaches, hneV, hp1NZ] using hrk
        let sl := par (vid w)
        have hwAct : vid w ∈ active := hi.verticesActive w hw
        have hwV : isVertex s.n (vid w) := by unfold isVertex vid; omega
        have hslEdge : isEdgeSlot s.n sl := hi.vertexParEdge (vid w) hwV hp1NZ
        have hslAct : sl ∈ active := hi.subPar_mem_active hwAct hp1NZ
        have hslNeU : sl ≠ vid u := fun h => not_vertex_and_edge ⟨by unfold isVertex vid; omega, h ▸ hslEdge⟩
        have hk1Pos : ∃ j, k1 = j + 1 := by
          cases k1 with
          | zero => exact absurd (by simpa [reaches] using hr1 : sl = vid u) hslNeU
          | succ j => exact ⟨j, rfl⟩
        obtain ⟨j, rfl⟩ := hk1Pos
        obtain ⟨hp2NZ, hp2V⟩ := hi.edgeParVertex sl hslAct hslEdge
        have hr2 : reaches par j (vid u) (par sl) = true := by
          have hbeq1 : (sl == vid u) = false := beq_false_of_ne hslNeU
          have hbeq2 : (par sl == 0) = false := beq_false_of_ne hp2NZ
          simpa [reaches, sl, hbeq1, hbeq2] using hr1
        let p := par sl - 1
        have hp2V' : 1 ≤ par sl ∧ par sl ≤ s.n := hp2V
        have hpLt : p < s.n := by dsimp only [p]; omega
        have hpid : vid p = par sl := by unfold vid; dsimp only [p]; omega
        obtain ⟨heE, hslotE⟩ := hn.inverse sl hslAct hslEdge
        let e := name sl
        have hpar_w : par (vid w) = slot e := hslotE.symm
        have hpar_sl : par (slot e) = vid p := by rw [hslotE, hpid]
        obtain ⟨walkP, hpathP, hvertsP, hedgesP, hdirP⟩ := ih j (by omega) p hpLt (hpid.symm ▸ hr2)
        have hident : (F.head e = w ∧ F.tail e = p) ∨ (F.tail e = w ∧ F.head e = p) := by
          obtain ⟨_, _, huniq⟩ := hi.edgeUniqueChild sl hslAct hslEdge
          have hchildW := huniq (vid w) ⟨hwAct, rfl, hwV,
            child_ne_parent_aux hi hslAct hwAct hslEdge rfl⟩
          have hve (x : ℕ) (hx : x < s.n) (hpx : par (vid x) = sl) : x = w := by
            have hcx := huniq (vid x) ⟨hi.verticesActive x hx, hpx, by unfold isVertex vid; omega,
              child_ne_parent_aux hi hslAct (hi.verticesActive x hx) hslEdge hpx⟩
            have hEq := hcx.trans hchildW.symm; unfold vid at hEq; omega
          have hends := hn.endpoints e heE; dsimp only at hends; rw [hslotE] at hends
          rcases hends with ⟨ht, hh⟩ | ⟨hh, ht⟩
          · refine Or.inr ⟨hve _ (hV e heE).1 ht, ?_⟩
            have hEq : vid (F.head e) = vid p := hh.symm.trans hpid.symm
            unfold vid at hEq; omega
          · refine Or.inl ⟨hve _ (hV e heE).2.1 hh, ?_⟩
            have hEq : vid (F.tail e) = vid p := ht.symm.trans hpid.symm
            unfold vid at hEq; omega
        have hwNotIn : w ∉ F.walkVertices u walkP := by
          intro hmem
          have hrwp := hvertsP w hmem
          have hle : depth (vid w) ≤ depth (vid p) :=
            depth_le_of_reaches_aux hmem_sub hi.acyclic N (vid w) (vid p) (hi.verticesActive p hpLt) hrwp
          have hd1 : depth sl < depth (vid w) := hi.acyclic (vid w) hwAct hp1NZ
          have hd2 : depth (vid p) < depth sl := hpid ▸ hi.acyclic sl hslAct hp2NZ
          omega
        let dir : Bool := decide (F.head e = w ∧ F.tail e = p)
        have hstepWalk : F.IsWalk p w [(e, dir)] := by
          rcases hident with ⟨hh, ht⟩ | ⟨ht, hh⟩
          · have hd : dir = true := by simp [dir, hh, ht]
            rw [hd]
            refine .cons heE (by simp [MGraph.src, ht]) ?_
            rw [show F.dst (e, true) = w by simp [MGraph.dst, hh]]; exact .nil w
          · have hne : ¬ (F.head e = w ∧ F.tail e = p) := fun ⟨hh', _⟩ => (hV e heE).2.2 (ht.trans hh'.symm)
            have hd : dir = false := by simp only [dir, hne, decide_false]
            rw [hd]
            refine .cons heE (by simp [MGraph.src, hh]) ?_
            rw [show F.dst (e, false) = w by simp [MGraph.dst, ht]]; exact .nil w
        have hwalk' : F.IsWalk u w (walkP ++ [(e, dir)]) := MGraph.isWalk_append hpathP.1 hstepWalk
        have hvertsEq : F.walkVertices u (walkP ++ [(e, dir)]) = F.walkVertices u walkP ++ [w] :=
          walkVertices_append_single hpathP.1 hstepWalk
        have hpath' : F.IsPath u w (walkP ++ [(e, dir)]) := by
          refine ⟨hwalk', ?_⟩
          rw [hvertsEq, List.nodup_append]
          exact ⟨hpathP.2, List.nodup_singleton w, fun a ha b hb => by
            simp only [List.mem_singleton] at hb; subst hb; intro h; exact hwNotIn (h ▸ ha)⟩
        refine ⟨walkP ++ [(e, dir)], hpath', fun z hz => ?_, fun f hf => ?_, fun x hx => ?_⟩
        · rw [hvertsEq, List.mem_append, List.mem_singleton] at hz
          rcases hz with hzP | rfl
          · have hr1' := (hstep_iff hslAct).mpr (Or.inr ⟨hp2NZ, hpid ▸ hvertsP z hzP⟩)
            exact (hstep_iff hwAct).mpr (Or.inr ⟨hp1NZ, hr1'⟩)
          · exact reaches_self par N (vid z)
        · have hneW : vid w ≠ slot f := fun h =>
            not_vertex_and_edge ⟨hwV, h ▸ (hn.forward f hf).2.1⟩
          rw [hstep_iff hwAct, or_iff_right hneW, and_iff_right hp1NZ,
            hstep_iff hslAct, and_iff_right hp2NZ, ← hpid, hedgesP f hf]
          simp only [walkEdges, List.map_append, List.map_cons, List.map_nil,
            List.toFinset_append, Finset.mem_union, List.mem_toFinset, List.mem_singleton]
          constructor
          · rintro (hEq | hm)
            · exact Or.inr (hslot_inj f hf e heE (hEq.symm.trans hslotE.symm))
            · exact Or.inl (by simpa [walkEdges] using hm)
          · rintro (hm | rfl)
            · exact Or.inr (by simpa [walkEdges] using hm)
            · exact Or.inl hslotE.symm
        · simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with hxP | rfl
          · exact hdirP x hxP
          · rcases hident with ⟨hh, ht⟩ | ⟨ht, hh⟩
            · have hd : dir = true := by simp only [dir, hh, ht, and_self, decide_true]
              simp [hd, hh, ht, hpar_w, hpar_sl]
            · have hne : ¬ (F.head e = w ∧ F.tail e = p) := fun ⟨hh', _⟩ => (hV e heE).2.2 (ht.trans hh'.symm)
              have hd : dir = false := by simp only [dir, hne, decide_false]
              simp [hd, hh, ht, hpar_w, hpar_sl]
  obtain ⟨walk, hpath, _, hedges, hdir⟩ := haux N v hv hreach
  have hfp : walk = F.forestPath u v := (LSF.forestPath_eq_of_isPath hF hpath).symm
  rw [← hfp]
  refine ⟨hedges, fun e he hmem => ?_⟩
  simp only [walkEdges, List.mem_toFinset, List.mem_map] at hmem
  obtain ⟨⟨e', b⟩, hxb, rfl⟩ := hmem
  have hwf := walkFlow_of_isPath_mem hpath hxb
  have hd := hdir (e', b) hxb
  constructor
  · intro ⟨h1, _⟩
    cases b with
    | true => simpa using hwf
    | false =>
      have ⟨h2, _⟩ := hd.2 rfl
      have hne : vid (F.head e') ≠ vid (F.tail e') := fun h =>
        (hV e' he).2.2 (by unfold vid at h; omega : F.head e' = F.tail e').symm
      obtain ⟨_, _, huniq⟩ := hi.edgeUniqueChild (slot e') (hn.forward e' he).1 (hn.forward e' he).2.1
      have hc1 := huniq (vid (F.head e')) ⟨hi.verticesActive _ (hV e' he).2.1, h1,
        by unfold isVertex vid; have := (hV e' he).2.1; omega,
        child_ne_parent_aux hi (hn.forward e' he).1 (hi.verticesActive _ (hV e' he).2.1)
          (hn.forward e' he).2.1 h1⟩
      have hc2 := huniq (vid (F.tail e')) ⟨hi.verticesActive _ (hV e' he).1, h2,
        by unfold isVertex vid; have := (hV e' he).1; omega,
        child_ne_parent_aux hi (hn.forward e' he).1 (hi.verticesActive _ (hV e' he).1)
          (hn.forward e' he).2.1 h2⟩
      exact absurd (hc1.trans hc2.symm) hne
  · intro ⟨h1, _⟩
    cases b with
    | false => simpa using hwf
    | true =>
      have ⟨h2, _⟩ := hd.1 rfl
      have hne : vid (F.tail e') ≠ vid (F.head e') := fun h =>
        (hV e' he).2.2 (by unfold vid at h; omega : F.tail e' = F.head e')
      obtain ⟨_, _, huniq⟩ := hi.edgeUniqueChild (slot e') (hn.forward e' he).1 (hn.forward e' he).2.1
      have hc1 := huniq (vid (F.tail e')) ⟨hi.verticesActive _ (hV e' he).1, h1,
        by unfold isVertex vid; have := (hV e' he).1; omega,
        child_ne_parent_aux hi (hn.forward e' he).1 (hi.verticesActive _ (hV e' he).1)
          (hn.forward e' he).2.1 h1⟩
      have hc2 := huniq (vid (F.head e')) ⟨hi.verticesActive _ (hV e' he).2.1, h2,
        by unfold isVertex vid; have := (hV e' he).2.1; omega,
        child_ne_parent_aux hi (hn.forward e' he).1 (hi.verticesActive _ (hV e' he).2.1)
          (hn.forward e' he).2.1 h2⟩
      exact absurd (hc1.trans hc2.symm) hne

/-- Rerooting a tree preserves `TreeEditNamedSlots` and every tree edge's orientation invariant,
`originalFlow`, `originalGradient`, `length`, and `detector`. -/
theorem reroot_preserves_named_orient {s : PathTreeState} {trees trees' : List AuxTree}
    {free : List ℕ} {depth depth' : ℕ → ℕ} {F : MGraph} {slot name : ℕ → ℕ} {u : ℕ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hn : TreeEditNamedSlots s trees F slot name)
    (hV : ∀ e ∈ F.E, F.tail e < s.n ∧ F.head e < s.n ∧ F.tail e ≠ F.head e)
    (hu : u < s.n)
    (hi' : LctInvWith pathPayload (lctReroot pathPayload s (vid u)) trees' free depth') :
    TreeEditNamedSlots (lctReroot pathPayload s (vid u)) trees' F slot name ∧
    ∀ e ∈ F.E, ∀ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
      ((val.forward = true →
          inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
       (val.forward = false →
          inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e))) →
      ∃ val' : PathEdgeValue,
        (slot e, some val') ∈ forestPairs pathPayload (lctReroot pathPayload s (vid u)).splay trees' ∧
        val'.originalFlow = val.originalFlow ∧
        val'.originalGradient = val.originalGradient ∧
        val'.length = val.length ∧
        val'.detector = val.detector ∧
        (val'.forward = true →
          inducedSubPar pathPayload (lctReroot pathPayload s (vid u)).splay trees' (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload (lctReroot pathPayload s (vid u)).splay trees' (slot e) = vid (F.tail e)) ∧
        (val'.forward = false →
          inducedSubPar pathPayload (lctReroot pathPayload s (vid u)).splay trees' (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload (lctReroot pathPayload s (vid u)).splay trees' (slot e) = vid (F.head e)) := by
  obtain ⟨ts, ds, hts, hperm, harc⟩ := treeEdit_reroot_edge_endpoints hi hu
  obtain ⟨hperm2, hpar2⟩ := treeEdit_witness_agreement hts hi'
  have hactPerm : (trees'.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) :=
    hperm2.symm.trans hperm
  have hns' : TreeEditNamedSlots (lctReroot pathPayload s (vid u)) trees' F slot name := by
    refine ⟨fun e he => ?_, fun k hk hks => hn.inverse k (hactPerm.mem_iff.mp hk) hks, fun e he => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hn.forward e he
      exact ⟨hactPerm.mem_iff.mpr h1, h2, h3⟩
    · obtain ⟨htLt, hhLt, _⟩ := hV e he
      have htV : isVertex s.n (vid (F.tail e)) := by unfold isVertex vid; omega
      have hhV : isVertex s.n (vid (F.head e)) := by unfold isVertex vid; omega
      rcases hn.endpoints e he with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · have h := harc (slot e) (hn.forward e he).1 (hn.forward e he).2.1 _ _ htV hhV h1 h2
        rw [hpar2] at h; exact h
      · have h := harc (slot e) (hn.forward e he).1 (hn.forward e he).2.1 _ _ hhV htV h1 h2
        rw [hpar2] at h; exact h.symm
  refine ⟨hns', fun e he val hp ⟨hft, hff⟩ => ?_⟩
  obtain ⟨htLt, hhLt, hne⟩ := hV e he
  have htV : isVertex s.n (vid (F.tail e)) := by unfold isVertex vid; omega
  have hhV : isVertex s.n (vid (F.head e)) := by unfold isVertex vid; omega
  have hneV : vid (F.head e) ≠ vid (F.tail e) := fun h =>
    hne (by unfold vid at h; omega : F.head e = F.tail e).symm
  cases hvf : val.forward with
  | true =>
    obtain ⟨hc, hpa⟩ := hft hvf
    obtain ⟨as, ad, haInv, hcases⟩ :=
      treeEdit_reroot_account_endpoints hi hu (hn.forward e he).1 (hn.forward e he).2.1 hhV htV hneV hc hpa hp
    obtain ⟨_, hap⟩ := treeEdit_witness_agreement haInv hi'
    have hfp := treeEdit_account_witness_agreement haInv hi'
    rw [hap] at hcases
    rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · refine ⟨val, hfp.mem_iff.mp h3, rfl, rfl, rfl, rfl, fun _ => ⟨h1, h2⟩, fun h => ?_⟩
      rw [hvf] at h; cases h
    · refine ⟨val.reverse, hfp.mem_iff.mp h3, val.originalFlow_reverse, val.originalGradient_reverse,
        rfl, rfl, fun h => ?_, fun _ => ⟨h1, h2⟩⟩
      simp [PathEdgeValue.reverse, hvf] at h
  | false =>
    obtain ⟨hc, hpa⟩ := hff hvf
    obtain ⟨as, ad, haInv, hcases⟩ :=
      treeEdit_reroot_account_endpoints hi hu (hn.forward e he).1 (hn.forward e he).2.1 htV hhV hneV.symm hc hpa hp
    obtain ⟨_, hap⟩ := treeEdit_witness_agreement haInv hi'
    have hfp := treeEdit_account_witness_agreement haInv hi'
    rw [hap] at hcases
    rcases hcases with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
    · refine ⟨val, hfp.mem_iff.mp h3, rfl, rfl, rfl, rfl, fun h => ?_, fun _ => ⟨h1, h2⟩⟩
      rw [hvf] at h; cases h
    · refine ⟨val.reverse, hfp.mem_iff.mp h3, val.originalFlow_reverse, val.originalGradient_reverse,
        rfl, rfl, fun _ => ⟨h1, h2⟩, fun h => ?_⟩
      simp [PathEdgeValue.reverse, hvf] at h

private theorem lctPathApply_eq_cost (s : PathTreeState) (u v : ℕ) (tag : PathTag) :
    lctPathApply pathPayload s u v tag = (lctPathApplyCost pathPayload s u v tag).1 := rfl

private theorem lctPathApply_splay_eq (s : PathTreeState) (u v : ℕ) (tag : PathTag) :
    ((lctPathApplyCost pathPayload s u v tag).1).splay =
      SplayState.applyTagNode pathPayload
        ((lctExposeCost pathPayload (lctRerootCost pathPayload s u).1 v).1).splay v tag := rfl

/-- Applying a lazy tag at `vid v` preserves `inducedSubPar` and auxiliary tree membership. -/
private theorem lctPathApply_same_trees_and_par
    {st2 s' : PathTreeState} {trees2 trees' : List AuxTree} {free : List ℕ} {depth2 depth' : ℕ → ℕ}
    {v : ℕ} {tag : PathTag}
    (hi2 : LctInvWith pathPayload st2 trees2 free depth2)
    (hi' : LctInvWith pathPayload s' trees' free depth')
    (hn : s'.n = st2.n)
    (hsp : s'.splay = SplayState.applyTagNode pathPayload st2.splay (vid v) tag) :
    (∀ t ∈ trees2, t ∈ trees') ∧
    (∀ t ∈ trees', t ∈ trees2) ∧
    inducedSubPar pathPayload s'.splay trees' = inducedSubPar pathPayload st2.splay trees2 := by
  have hst2_nodes : ∀ x,
      (s'.splay.nodes x).left = (st2.splay.nodes x).left ∧
      (s'.splay.nodes x).right = (st2.splay.nodes x).right ∧
      (s'.splay.nodes x).par = (st2.splay.nodes x).par ∧
      (s'.splay.nodes x).ppar = (st2.splay.nodes x).ppar ∧
      (s'.splay.nodes x).rev = (st2.splay.nodes x).rev := by
    intro x
    rw [hsp]
    unfold SplayState.applyTagNode SplayState.updateNode
    by_cases hx : x = v + 1 <;> simp [vid, hx]
  have hmem_2 : ∀ t ∈ trees2, t ∈ trees' := fun t ht =>
    lct_tree_mem_of_same_pointers hi' hi2 hn.symm
      (fun x => (hst2_nodes x).1) (fun x => (hst2_nodes x).2.1) (fun x => (hst2_nodes x).2.2.1) ht
  have hmem_1 : ∀ t ∈ trees', t ∈ trees2 := fun t ht =>
    lct_tree_mem_of_same_pointers hi2 hi' hn
      (fun x => (hst2_nodes x).1.symm) (fun x => (hst2_nodes x).2.1.symm) (fun x => (hst2_nodes x).2.2.1.symm) ht
  refine ⟨hmem_2, hmem_1, funext fun z => ?_⟩
  by_cases hz : z ∈ trees'.flatMap AuxTree.toList
  · obtain ⟨t, ht, hzt⟩ := List.mem_flatMap.mp hz
    have hp1 := inducedSubPar_eq_of_mem (P := pathPayload) (s := s'.splay) hi'.activeNodup ht hzt
    have hp2 := inducedSubPar_eq_of_mem (P := pathPayload) (s := st2.splay) hi2.activeNodup (hmem_1 t ht) hzt
    rw [hp1, hp2, LinkCut.PathProg.treeIds_shape pathPayload (fun y => (hst2_nodes y).2.2.2.2) t,
      (hst2_nodes t.rootId).2.2.2.1]
  · have hz2 : z ∉ trees2.flatMap AuxTree.toList := fun h => by
      obtain ⟨t, ht, hzt⟩ := List.mem_flatMap.mp h
      exact hz (List.mem_flatMap.mpr ⟨t, hmem_2 t ht, hzt⟩)
    rw [inducedSubPar_eq_zero_of_not_mem hz, inducedSubPar_eq_zero_of_not_mem hz2]

/-- Core step accounting abstracted over the three intermediate `PathTreeState`s so the kernel
never unfolds `lctRerootCost`/`lctExposeCost`/`lctPathApplyCost`. -/
private theorem lctPathApply_step_account_core
    {s st1 st2 s' : PathTreeState}
    {trees trees1 trees2 treesA trees' : List AuxTree} {Lv La : AuxTree}
    {free : List ℕ} {depth depth1 depth2 depthA depth' : ℕ → ℕ}
    {F : MGraph} {slot name : ℕ → ℕ} {u v : ℕ} {mult : ℤ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hF : F.IsForest)
    (hV : ∀ e ∈ F.E, F.tail e < s.n ∧ F.head e < s.n ∧ F.tail e ≠ F.head e)
    (hu : u < s.n) (hv : v < s.n)
    (hsubEq : subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length (vid u) =
      subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length (vid v))
    (hs2n : st2.n = s.n) (hs'n : s'.n = st2.n)
    (hs'sp : s'.splay = SplayState.applyTagNode pathPayload st2.splay (vid v) (PathTag.ofFlow mult))
    (hi1 : LctInvWith pathPayload st1 trees1 free depth1)
    (hact1 : (trees1.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList))
    (hpar1_u : inducedSubPar pathPayload st1.splay trees1 (vid u) = 0)
    (hconn1 : ∀ x ∈ trees.flatMap AuxTree.toList, ∀ y ∈ trees.flatMap AuxTree.toList,
      subRoot (inducedSubPar pathPayload st1.splay trees1) (trees1.flatMap AuxTree.toList).length x =
        subRoot (inducedSubPar pathPayload st1.splay trees1) (trees1.flatMap AuxTree.toList).length y ↔
      subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length x =
        subRoot (inducedSubPar pathPayload s.splay trees) (trees.flatMap AuxTree.toList).length y)
    (hor1 : ∀ e ∈ F.E, ∀ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
      ((val.forward = true →
          inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
       (val.forward = false →
          inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e))) →
      ∃ val1 : PathEdgeValue,
        (slot e, some val1) ∈ forestPairs pathPayload st1.splay trees1 ∧
        val1.originalFlow = val.originalFlow ∧
        val1.originalGradient = val.originalGradient ∧
        val1.length = val.length ∧
        val1.detector = val.detector ∧
        (val1.forward = true →
          inducedSubPar pathPayload st1.splay trees1 (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload st1.splay trees1 (slot e) = vid (F.tail e)) ∧
        (val1.forward = false →
          inducedSubPar pathPayload st1.splay trees1 (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload st1.splay trees1 (slot e) = vid (F.head e)))
    (ht2 : AuxTree.node (vid v) Lv AuxTree.leaf ∈ trees2)
    (hi2 : LctInvWith pathPayload st2 trees2 free depth2)
    (hact2 : (trees2.flatMap AuxTree.toList).Perm (trees1.flatMap AuxTree.toList))
    (hpar2 : ∀ x, inducedSubPar pathPayload st2.splay trees2 x = inducedSubPar pathPayload st1.splay trees1 x)
    (hfp2 : (forestPairs pathPayload st2.splay trees2).Perm (forestPairs pathPayload st1.splay trees1))
    (hreach2 : ∀ z, z ∈ (AuxTree.node (vid v) Lv AuxTree.leaf).toList ↔
      reaches (inducedSubPar pathPayload st1.splay trees1) (trees1.flatMap AuxTree.toList).length z (vid v) = true)
    (hns2 : TreeEditNamedSlots st2 trees2 F slot name)
    (htA : AuxTree.node (vid v) La AuxTree.leaf ∈ treesA)
    (hiA : LctInvWith pathPayload s' treesA free depthA)
    (hactA : (treesA.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList))
    (hfpA : (forestPairs pathPayload s'.splay treesA).Perm
      ((SplayState.evalPairs pathPayload st2.splay (AuxTree.node (vid v) La AuxTree.leaf) false pathPayload.idTag).map
        (fun p => (p.1, pathPayload.actVal (PathTag.ofFlow mult) p.2)) ++
       forestPairs pathPayload st2.splay (treesA.erase (AuxTree.node (vid v) La AuxTree.leaf))))
    (hfpExpA : (forestPairs pathPayload st2.splay treesA).Perm
      (SplayState.evalPairs pathPayload st2.splay (AuxTree.node (vid v) La AuxTree.leaf) false pathPayload.idTag ++
       forestPairs pathPayload st2.splay (treesA.erase (AuxTree.node (vid v) La AuxTree.leaf))))
    (hoffA : ∀ p ∈ forestPairs pathPayload st2.splay (treesA.erase (AuxTree.node (vid v) La AuxTree.leaf)),
      p.1 ∉ (AuxTree.node (vid v) La AuxTree.leaf).toList)
    (honA : ∀ p ∈ SplayState.evalPairs pathPayload st2.splay (AuxTree.node (vid v) La AuxTree.leaf) false pathPayload.idTag,
      p.1 ∈ (AuxTree.node (vid v) La AuxTree.leaf).toList)
    (hi' : LctInvWith pathPayload s' trees' free depth') :
    TreeEditNamedSlots s' trees' F slot name ∧
    ∀ e ∈ F.E, ∀ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
      ((val.forward = true →
          inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
       (val.forward = false →
          inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e))) →
      ∃ val' : PathEdgeValue,
        (slot e, some val') ∈ forestPairs pathPayload s'.splay trees' ∧
        (val'.originalFlow : ℝ) = (val.originalFlow : ℝ) + (mult : ℝ) * walkFlow (F.forestPath u v) e ∧
        (val'.detector : ℝ) = (val.detector : ℝ) + |(mult : ℝ) * walkFlow (F.forestPath u v) e| ∧
        val'.originalGradient = val.originalGradient ∧
        val'.length = val.length ∧
        (val'.forward = true →
          inducedSubPar pathPayload s'.splay trees' (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.tail e)) ∧
        (val'.forward = false →
          inducedSubPar pathPayload s'.splay trees' (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.head e)) := by
  have hv1 : vid v ∈ trees1.flatMap AuxTree.toList := hact1.symm.mem_iff.mp (hi.verticesActive v hv)
  let t_exp := AuxTree.node (vid v) Lv AuxTree.leaf
  obtain ⟨hmem_2, hmem_1, hpar2_eq⟩ := lctPathApply_same_trees_and_par hi2 hi' hs'n hs'sp
  obtain ⟨hactA', _⟩ := treeEdit_witness_agreement hiA hi'
  have hfpA' := treeEdit_account_witness_agreement hiA hi'
  have hact_eq : (trees'.flatMap AuxTree.toList).Perm (trees2.flatMap AuxTree.toList) :=
    hactA'.symm.trans (hactA.trans (hact1.symm.trans hact2.symm))
  have hns' : TreeEditNamedSlots s' trees' F slot name := by
    refine ⟨fun e he => ?_, fun k hk hks => hns2.inverse k (hact_eq.mem_iff.mp hk) (hs'n ▸ hks), fun e he => ?_⟩
    · obtain ⟨h1, h2, h3⟩ := hns2.forward e he
      exact ⟨hact_eq.mem_iff.mpr h1, hs'n.symm ▸ h2, h3⟩
    · have he2 := hns2.endpoints e he; dsimp only at he2 ⊢; rw [hpar2_eq]; exact he2
  have hpar2_fun : inducedSubPar pathPayload st2.splay trees2 = inducedSubPar pathPayload st1.splay trees1 :=
    funext hpar2
  have hpar2_u : inducedSubPar pathPayload st2.splay trees2 (vid u) = 0 := by rw [hpar2_fun]; exact hpar1_u
  have hreach2_uv : reaches (inducedSubPar pathPayload st2.splay trees2)
      (trees2.flatMap AuxTree.toList).length (vid u) (vid v) = true := by
    have h1 := (hconn1 (vid u) (hi.verticesActive u hu) (vid v) (hi.verticesActive v hv)).mpr hsubEq
    have hsu : subRoot (inducedSubPar pathPayload st1.splay trees1) (trees1.flatMap AuxTree.toList).length (vid u) = vid u :=
      subRoot_eq_self_of_zero hi1 (hact1.symm.mem_iff.mp (hi.verticesActive u hu)) hpar1_u
    rw [hsu] at h1
    have hr1 := (subRoot_eq_iff_reaches_zero hi1 hv1 hpar1_u).mp h1.symm
    rw [hpar2_fun, hact2.length_eq]; exact hr1
  obtain ⟨hwalk_iff, hwalk_dir⟩ := parentWalk_forestPath hi2 hns2 hF (hs2n.symm ▸ hV) (hs2n.symm ▸ hu) (hs2n.symm ▸ hv) hpar2_u hreach2_uv
  have htA_eq : AuxTree.node (vid v) La AuxTree.leaf = t_exp := by
    have hmemA' : AuxTree.node (vid v) La AuxTree.leaf ∈ trees' :=
      lct_tree_mem_of_same_pointers hi' hiA rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) htA
    exact flatMap_mem_unique hi2.activeNodup (hmem_1 _ hmemA') ht2 (x := vid v) (by simp [AuxTree.toList]) (by simp [t_exp, AuxTree.toList])
  have hmem_st2_A : ∀ p, p ∈ forestPairs pathPayload st2.splay trees2 →
      p ∈ forestPairs pathPayload st2.splay treesA := by
    intro p hp
    obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp hp
    have htA' : t ∈ treesA :=
      lct_tree_mem_of_same_pointers hiA hi' rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (hmem_2 t ht)
    exact List.mem_flatMap.mpr ⟨t, htA', hpt⟩
  refine ⟨hns', fun e he val hp hor => ?_⟩
  obtain ⟨val1, hp1, hfl1, hgr1, hlen1, hdet1, hft1, hff1⟩ := hor1 e he val hp hor
  have hp2 : (slot e, some val1) ∈ forestPairs pathPayload st2.splay trees2 := hfp2.mem_iff.mpr hp1
  have hpExp : (slot e, some val1) ∈
      SplayState.evalPairs pathPayload st2.splay (AuxTree.node (vid v) La AuxTree.leaf) false pathPayload.idTag ++
      forestPairs pathPayload st2.splay (treesA.erase (AuxTree.node (vid v) La AuxTree.leaf)) :=
    hfpExpA.mem_iff.mp (hmem_st2_A _ hp2)
  by_cases hin : e ∈ walkEdges (F.forestPath u v)
  · have hmemExp : slot e ∈ (AuxTree.node (vid v) La AuxTree.leaf).toList := by
      rw [htA_eq]; apply (hreach2 (slot e)).mpr
      have hr := (hwalk_iff e he).mpr hin
      rw [hpar2_fun, hact2.length_eq] at hr; exact hr
    have hnotOff : (slot e, some val1) ∉
        forestPairs pathPayload st2.splay (treesA.erase (AuxTree.node (vid v) La AuxTree.leaf)) :=
      fun h => hoffA _ h hmemExp
    have hon := (List.mem_append.mp hpExp).resolve_right hnotOff
    let val' := val1.shift (PathTag.ofFlow mult)
    have hpA : (slot e, some val') ∈ forestPairs pathPayload s'.splay treesA :=
      hfpA.mem_iff.mpr (List.mem_append_left _ (List.mem_map.mpr ⟨(slot e, some val1), hon, rfl⟩))
    have hp' := hfpA'.mem_iff.mp hpA
    have hwf_val : walkFlow (F.forestPath u v) e = if val1.forward then 1 else -1 := by
      cases hvf : val1.forward with
      | true =>
        have ⟨h1, h2⟩ := hft1 hvf
        rw [← hpar2_fun] at h1 h2
        simpa using (hwalk_dir e he hin).1 ⟨h1, h2⟩
      | false =>
        have ⟨h1, h2⟩ := hff1 hvf
        rw [← hpar2_fun] at h1 h2
        simpa using (hwalk_dir e he hin).2 ⟨h1, h2⟩
    refine ⟨val', hp', ?_, ?_, hgr1, hlen1,
      fun hf => by rw [hpar2_eq, hpar2_fun]; exact hft1 hf,
      fun hf => by rw [hpar2_eq, hpar2_fun]; exact hff1 hf⟩
    · have hsh := PathEdgeValue.originalFlow_shift val1 (PathTag.ofFlow mult)
      rw [hsh, hfl1, hwf_val]
      cases val1.forward <;> simp [PathTag.ofFlow]
    · simp only [val', PathEdgeValue.shift, PathTag.ofFlow, Int.cast_add, Int.cast_abs, hdet1, hwf_val]
      cases val1.forward <;> simp
  · have hnotExp : slot e ∉ (AuxTree.node (vid v) La AuxTree.leaf).toList := by
      rw [htA_eq]; intro hmem
      have hr := (hreach2 (slot e)).mp hmem
      rw [← hpar2_fun, ← hact2.length_eq] at hr
      exact hin ((hwalk_iff e he).mp hr)
    have hnotOn : (slot e, some val1) ∉
        SplayState.evalPairs pathPayload st2.splay (AuxTree.node (vid v) La AuxTree.leaf) false pathPayload.idTag :=
      fun h => hnotExp (honA _ h)
    have hoff := (List.mem_append.mp hpExp).resolve_left hnotOn
    have hpA : (slot e, some val1) ∈ forestPairs pathPayload s'.splay treesA :=
      hfpA.mem_iff.mpr (List.mem_append_right _ hoff)
    have hp' := hfpA'.mem_iff.mp hpA
    have hwf0 : walkFlow (F.forestPath u v) e = 0 := walkFlow_eq_zero_of_not_mem hin
    refine ⟨val1, hp', ?_, ?_, hgr1, hlen1,
      fun hf => by rw [hpar2_eq, hpar2_fun]; exact hft1 hf,
      fun hf => by rw [hpar2_eq, hpar2_fun]; exact hff1 hf⟩
    · simp [hfl1, hwf0]
    · simp [hdet1, hwf0]

private theorem lctRerootCost_n (s : PathTreeState) (u : ℕ) :
    (lctRerootCost pathPayload s u).1.n = s.n := rfl

private theorem lctExposeCost_n (s : PathTreeState) (v : ℕ) :
    (lctExposeCost pathPayload s v).1.n = s.n := rfl

private theorem lctPathApplyCost_n (s : PathTreeState) (u v : ℕ) (tag : PathTag) :
    (lctPathApplyCost pathPayload s u v tag).1.n = s.n := rfl

/-- One step of `lctPathApply pathPayload s (vid u) (vid v) (PathTag.ofFlow mult)` preserves
`TreeEditNamedSlots` and orientation/gradient/length, and updates every tree edge `e ∈ F.E`
by `mult * walkFlow (F.forestPath u v) e` in `originalFlow` and `|mult * walkFlow ...|` in `detector`. -/
theorem lctPathApply_step_account {s : PathTreeState} {trees trees' : List AuxTree}
    {free : List ℕ} {depth depth' : ℕ → ℕ} {F : MGraph} {slot name : ℕ → ℕ}
    {u v : ℕ} {mult : ℤ}
    (hi : LctInvWith pathPayload s trees free depth)
    (hn : TreeEditNamedSlots s trees F slot name)
    (hF : F.IsForest)
    (hV : ∀ e ∈ F.E, F.tail e < s.n ∧ F.head e < s.n ∧ F.tail e ≠ F.head e)
    (hu : u < s.n) (hv : v < s.n) (hconn : F.Connected u v)
    (hi' : LctInvWith pathPayload (lctPathApply pathPayload s (vid u) (vid v) (PathTag.ofFlow mult)) trees' free depth') :
    let s' := lctPathApply pathPayload s (vid u) (vid v) (PathTag.ofFlow mult)
    TreeEditNamedSlots s' trees' F slot name ∧
    ∀ e ∈ F.E, ∀ val : PathEdgeValue,
      (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
      ((val.forward = true →
          inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
       (val.forward = false →
          inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e))) →
      ∃ val' : PathEdgeValue,
        (slot e, some val') ∈ forestPairs pathPayload s'.splay trees' ∧
        (val'.originalFlow : ℝ) = (val.originalFlow : ℝ) + (mult : ℝ) * walkFlow (F.forestPath u v) e ∧
        (val'.detector : ℝ) = (val.detector : ℝ) + |(mult : ℝ) * walkFlow (F.forestPath u v) e| ∧
        val'.originalGradient = val.originalGradient ∧
        val'.length = val.length ∧
        (val'.forward = true →
          inducedSubPar pathPayload s'.splay trees' (vid (F.head e)) = slot e ∧
          inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.tail e)) ∧
        (val'.forward = false →
          inducedSubPar pathPayload s'.splay trees' (vid (F.tail e)) = slot e ∧
          inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.head e)) := by
  dsimp only
  have hrr : lctReroot pathPayload s (vid u) = (lctRerootCost pathPayload s (vid u)).1 := rfl
  have hex : lctExpose pathPayload (lctRerootCost pathPayload s (vid u)).1 (vid v) =
      (lctExposeCost pathPayload (lctRerootCost pathPayload s (vid u)).1 (vid v)).1 := rfl
  rw [lctPathApply_eq_cost] at hi' ⊢
  have huV : isVertex s.n (vid u) := by unfold isVertex vid; omega
  have hconnT : pathTreeConnected s (vid u) (vid v) :=
    treeEditNamedSlots_connected hi hn (fun e he => ⟨(hV e he).1, (hV e he).2.1⟩) hu hv hconn
  have hsubEq := (pathTreeConnected_iff_induced_roots hi hu hv).mp hconnT
  obtain ⟨tu, htu, huMem⟩ := List.mem_flatMap.mp (hi.verticesActive u hu)
  obtain ⟨tv, htv, hvMem⟩ := List.mem_flatMap.mp (hi.verticesActive v hv)
  obtain ⟨trees1, _, depth1, _, hi1, hact1, _, hpar1_u, _, _, _, _, _, _, _, _, _, hconn1, _, _⟩ :=
    lctReroot_spec pathPayload_laws hi htu huMem huV
  obtain ⟨hns1, hor1⟩ := reroot_preserves_named_orient hi hn hV hu (hrr ▸ hi1)
  rw [hrr] at hns1 hor1
  have hv1 : vid v ∈ trees1.flatMap AuxTree.toList := hact1.symm.mem_iff.mp (hi.verticesActive v hv)
  obtain ⟨tv1, htv1, hv1Mem⟩ := List.mem_flatMap.mp hv1
  obtain ⟨trees2, Lv, ht2, hi2, hact2, hpar2, hfp2, _, _, _, _, hreach2, _, _, _⟩ :=
    lctExpose_spec pathPayload_laws hi1 htv1 hv1Mem
  have hns2 : TreeEditNamedSlots (lctExposeCost pathPayload (lctRerootCost pathPayload s (vid u)).1 (vid v)).1
      trees2 F slot name := by
    have h := treeEditNamedSlots_expose_witness hns1 hi1 hv1 (hex ▸ hi2)
    rw [hex] at h; exact h
  obtain ⟨treesA, La, depthA, htA, hiA, hactA, _, _, _, _, _, hfpA, hfpExpA, hoffA, honA, _, _, _⟩ :=
    lctPathApply_spec pathPayload_laws hi htu huMem huV htv hvMem hsubEq (PathTag.ofFlow mult)
  have hs2n : (lctExposeCost pathPayload (lctRerootCost pathPayload s (vid u)).1 (vid v)).1.n = s.n :=
    (lctExposeCost_n _ _).trans (lctRerootCost_n _ _)
  have hs'n : (lctPathApplyCost pathPayload s (vid u) (vid v) (PathTag.ofFlow mult)).1.n =
      (lctExposeCost pathPayload (lctRerootCost pathPayload s (vid u)).1 (vid v)).1.n :=
    (lctPathApplyCost_n _ _ _ _).trans hs2n.symm
  exact lctPathApply_step_account_core hi hF hV hu hv hsubEq hs2n hs'n
    (lctPathApply_splay_eq s (vid u) (vid v) (PathTag.ofFlow mult))
    hi1 hact1 hpar1_u hconn1 hor1 ht2 hi2 hact2 hpar2 hfp2 hreach2 hns2
    htA hiA hactA hfpA hfpExpA hoffA honA hi'

/-- Folding `lctPathApply` with `PathTag.ofFlow mult` over `paths` preserves `TreeEditNamedSlots`
and orientation/gradient/length, and updates every tree edge's `originalFlow` and `detector`
by the exact signed and absolute path sums over `paths`. -/
theorem applyPathsFold_account {F : MGraph} {slot name : ℕ → ℕ} {mult : ℤ}
    (hF : F.IsForest) :
    ∀ (paths : List (ℕ × ℕ)) {s : PathTreeState} {trees trees' : List AuxTree}
      {free : List ℕ} {depth depth' : ℕ → ℕ},
      LctInvWith pathPayload s trees free depth →
      TreeEditNamedSlots s trees F slot name →
      (∀ e ∈ F.E, F.tail e < s.n ∧ F.head e < s.n ∧ F.tail e ≠ F.head e) →
      (∀ p ∈ paths, p.1 < s.n ∧ p.2 < s.n ∧ F.Connected p.1 p.2) →
      LctInvWith pathPayload (applyPathsFold s (PathTag.ofFlow mult) paths) trees' free depth' →
      let s' := applyPathsFold s (PathTag.ofFlow mult) paths
      TreeEditNamedSlots s' trees' F slot name ∧
      ∀ e ∈ F.E, ∀ val : PathEdgeValue,
        (slot e, some val) ∈ forestPairs pathPayload s.splay trees →
        ((val.forward = true →
            inducedSubPar pathPayload s.splay trees (vid (F.head e)) = slot e ∧
            inducedSubPar pathPayload s.splay trees (slot e) = vid (F.tail e)) ∧
         (val.forward = false →
            inducedSubPar pathPayload s.splay trees (vid (F.tail e)) = slot e ∧
            inducedSubPar pathPayload s.splay trees (slot e) = vid (F.head e))) →
        ∃ val' : PathEdgeValue,
          (slot e, some val') ∈ forestPairs pathPayload s'.splay trees' ∧
          (val'.originalFlow : ℝ) = (val.originalFlow : ℝ) +
            (mult : ℝ) * (paths.map (fun p => walkFlow (F.forestPath p.1 p.2) e)).sum ∧
          (val'.detector : ℝ) = (val.detector : ℝ) +
            (paths.map (fun p => |(mult : ℝ) * walkFlow (F.forestPath p.1 p.2) e|)).sum ∧
          val'.originalGradient = val.originalGradient ∧
          val'.length = val.length ∧
          (val'.forward = true →
            inducedSubPar pathPayload s'.splay trees' (vid (F.head e)) = slot e ∧
            inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.tail e)) ∧
          (val'.forward = false →
            inducedSubPar pathPayload s'.splay trees' (vid (F.tail e)) = slot e ∧
            inducedSubPar pathPayload s'.splay trees' (slot e) = vid (F.head e)) := by
  intro paths
  induction paths with
  | nil =>
    intro s trees trees' free depth depth' hi hn _ _ hi'
    simp only [applyPathsFold, List.foldl_nil] at hi' ⊢
    obtain ⟨hact, hpar⟩ := treeEdit_witness_agreement hi hi'
    have hfp := treeEdit_account_witness_agreement hi hi'
    refine ⟨⟨fun e he => by
        obtain ⟨h1, h2, h3⟩ := hn.forward e he; exact ⟨hact.mem_iff.mp h1, h2, h3⟩,
      fun k hk hks => hn.inverse k (hact.mem_iff.mpr hk) hks,
      fun e he => by have := hn.endpoints e he; dsimp only at this ⊢; rw [← hpar]; exact this⟩,
      fun e _ val hp ⟨hft, hff⟩ => ⟨val, hfp.mem_iff.mp hp, by simp, by simp, rfl, rfl,
        fun hf => by rw [← hpar]; exact hft hf, fun hf => by rw [← hpar]; exact hff hf⟩⟩
  | cons p rest ih =>
    intro s trees trees' free depth depth' hi hn hV hpaths hi'
    have hp0 := hpaths p List.mem_cons_self
    have hconnT := treeEditNamedSlots_connected hi hn (fun e he => ⟨(hV e he).1, (hV e he).2.1⟩)
      hp0.1 hp0.2.1 hp0.2.2
    have hsubEq := (pathTreeConnected_iff_induced_roots hi hp0.1 hp0.2.1).mp hconnT
    obtain ⟨tu, htu, huMem⟩ := List.mem_flatMap.mp (hi.verticesActive p.1 hp0.1)
    obtain ⟨tv, htv, hvMem⟩ := List.mem_flatMap.mp (hi.verticesActive p.2 hp0.2.1)
    obtain ⟨trees1, _, depth1, _, hi1, _⟩ :=
      lctPathApply_spec pathPayload_laws hi htu huMem (by unfold isVertex vid; omega)
        htv hvMem hsubEq (PathTag.ofFlow mult)
    let s1 := lctPathApply pathPayload s (vid p.1) (vid p.2) (PathTag.ofFlow mult)
    have hs1n : s1.n = s.n := rfl
    obtain ⟨hns1, hstep1⟩ := lctPathApply_step_account hi hn hF hV hp0.1 hp0.2.1 hp0.2.2 hi1
    have hrest : ∀ q ∈ rest, q.1 < s1.n ∧ q.2 < s1.n ∧ F.Connected q.1 q.2 :=
      fun q hq => hpaths q (List.mem_cons_of_mem _ hq)
    obtain ⟨hns2, hstep2⟩ := ih hi1 hns1 (hs1n.symm ▸ hV) hrest hi'
    refine ⟨hns2, fun e he val hp hor => ?_⟩
    obtain ⟨val1, hp1, hfl1, hdet1, hgr1, hlen1, hft1, hff1⟩ := hstep1 e he val hp hor
    obtain ⟨val2, hp2, hfl2, hdet2, hgr2, hlen2, hft2, hff2⟩ := hstep2 e he val1 hp1 ⟨hft1, hff1⟩
    refine ⟨val2, hp2, ?_, ?_, hgr2.trans hgr1, hlen2.trans hlen1, hft2, hff2⟩
    · simp only [List.map_cons, List.sum_cons, mul_add]
      linarith
    · simp only [List.map_cons, List.sum_cons]
      linarith

private theorem lctPathApply_some_back_core
    {s st1 st2 s' : PathTreeState}
    {trees trees1 trees2 treesA trees' : List AuxTree} {Lr La : AuxTree}
    {free : List ℕ} {depth2 depthA depth' : ℕ → ℕ}
    {u v : ℕ} {tag : PathTag}
    (hs'n : s'.n = st2.n)
    (hs'sp : s'.splay = SplayState.applyTagNode pathPayload st2.splay (vid v) tag)
    (hfpR0 : (SplayState.evalPairs pathPayload (lctExposeCost pathPayload s (vid u)).1.splay
        (AuxTree.node (vid u) Lr AuxTree.leaf) false pathPayload.idTag ++
      forestPairs pathPayload (lctExposeCost pathPayload s (vid u)).1.splay
        (trees1.erase (AuxTree.node (vid u) AuxTree.leaf Lr))).Perm (forestPairs pathPayload s.splay trees))
    (hfpR1 : (forestPairs pathPayload st1.splay trees1).Perm
      (((SplayState.evalPairs pathPayload (lctExposeCost pathPayload s (vid u)).1.splay
          (AuxTree.node (vid u) Lr AuxTree.leaf) false pathPayload.idTag).map
        (fun p => (p.1, pathPayload.revVal p.2))).reverse ++
      forestPairs pathPayload (lctExposeCost pathPayload s (vid u)).1.splay
        (trees1.erase (AuxTree.node (vid u) AuxTree.leaf Lr))))
    (hi2 : LctInvWith pathPayload st2 trees2 free depth2)
    (hfp2 : (forestPairs pathPayload st2.splay trees2).Perm (forestPairs pathPayload st1.splay trees1))
    (hiA : LctInvWith pathPayload s' treesA free depthA)
    (hfpA : (forestPairs pathPayload s'.splay treesA).Perm
      ((SplayState.evalPairs pathPayload st2.splay (AuxTree.node (vid v) La AuxTree.leaf) false pathPayload.idTag).map
        (fun p => (p.1, pathPayload.actVal tag p.2)) ++
       forestPairs pathPayload st2.splay (treesA.erase (AuxTree.node (vid v) La AuxTree.leaf))))
    (hfpExpA : (forestPairs pathPayload st2.splay treesA).Perm
      (SplayState.evalPairs pathPayload st2.splay (AuxTree.node (vid v) La AuxTree.leaf) false pathPayload.idTag ++
       forestPairs pathPayload st2.splay (treesA.erase (AuxTree.node (vid v) La AuxTree.leaf))))
    (hi' : LctInvWith pathPayload s' trees' free depth')
    {sl : ℕ} {val' : PathEdgeValue}
    (hp' : (sl, some val') ∈ forestPairs pathPayload s'.splay trees') :
    ∃ val : PathEdgeValue, (sl, some val) ∈ forestPairs pathPayload s.splay trees := by
  obtain ⟨_, hmem_1, _⟩ := lctPathApply_same_trees_and_par hi2 hi' hs'n hs'sp
  have hfpA' := treeEdit_account_witness_agreement hiA hi'
  have hpA := hfpA.mem_iff.mp (hfpA'.symm.mem_iff.mp hp')
  have hpSt2A : ∃ v2 : PathEdgeValue, (sl, some v2) ∈ forestPairs pathPayload st2.splay treesA := by
    rcases List.mem_append.mp hpA with hon | hoff
    · obtain ⟨⟨k, opt⟩, hmem, hEq⟩ := List.mem_map.mp hon
      simp only [Prod.mk.injEq] at hEq
      obtain ⟨rfl, hact⟩ := hEq
      cases opt with
      | none => simp [pathPayload] at hact
      | some v2 => exact ⟨v2, hfpExpA.symm.mem_iff.mp (List.mem_append_left _ hmem)⟩
    · exact ⟨val', hfpExpA.symm.mem_iff.mp (List.mem_append_right _ hoff)⟩
  obtain ⟨v2, hv2A⟩ := hpSt2A
  have hv2 : (sl, some v2) ∈ forestPairs pathPayload st2.splay trees2 := by
    obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp hv2A
    have ht' : t ∈ trees' :=
      lct_tree_mem_of_same_pointers hi' hiA rfl (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) ht
    exact List.mem_flatMap.mpr ⟨t, hmem_1 t ht', hpt⟩
  have hv1 : (sl, some v2) ∈ forestPairs pathPayload st1.splay trees1 := hfp2.mem_iff.mp hv2
  rcases List.mem_append.mp (hfpR1.mem_iff.mp hv1) with hrev | hoff
  · rw [List.mem_reverse] at hrev
    obtain ⟨⟨k, opt⟩, hmem, hEq⟩ := List.mem_map.mp hrev
    simp only [Prod.mk.injEq] at hEq
    obtain ⟨rfl, hrv⟩ := hEq
    cases opt with
    | none => simp [pathPayload] at hrv
    | some v0 => exact ⟨v0, hfpR0.mem_iff.mp (List.mem_append_left _ hmem)⟩
  · exact ⟨v2, hfpR0.mem_iff.mp (List.mem_append_right _ hoff)⟩

/-- Any active `some` payload after folding `lctPathApply` over `paths` came from a `some` payload
at the same node before the fold. -/
theorem applyPathsFold_some_back {F : MGraph} {slot name : ℕ → ℕ} {tag : PathTag} :
    ∀ (paths : List (ℕ × ℕ)) {s : PathTreeState} {trees trees' : List AuxTree}
      {free : List ℕ} {depth depth' : ℕ → ℕ},
      LctInvWith pathPayload s trees free depth →
      TreeEditNamedSlots s trees F slot name →
      (∀ e ∈ F.E, F.tail e < s.n ∧ F.head e < s.n) →
      (∀ p ∈ paths, p.1 < s.n ∧ p.2 < s.n ∧ F.Connected p.1 p.2) →
      LctInvWith pathPayload (applyPathsFold s tag paths) trees' free depth' →
      ∀ sl val', (sl, some val') ∈ forestPairs pathPayload (applyPathsFold s tag paths).splay trees' →
        ∃ val, (sl, some val) ∈ forestPairs pathPayload s.splay trees := by
  intro paths
  induction paths with
  | nil =>
    intro s trees trees' free depth depth' hi _ _ _ hi' sl val' hp'
    simp only [applyPathsFold, List.foldl_nil] at hi' hp'
    exact ⟨val', (treeEdit_account_witness_agreement hi hi').symm.mem_iff.mp hp'⟩
  | cons p rest ih =>
    intro s trees trees' free depth depth' hi hn hV hpaths hi' sl val' hp'
    have hp0 := hpaths p List.mem_cons_self
    have hconnT := treeEditNamedSlots_connected hi hn hV hp0.1 hp0.2.1 hp0.2.2
    have hsubEq := (pathTreeConnected_iff_induced_roots hi hp0.1 hp0.2.1).mp hconnT
    obtain ⟨tu, htu, huMem⟩ := List.mem_flatMap.mp (hi.verticesActive p.1 hp0.1)
    obtain ⟨tv, htv, hvMem⟩ := List.mem_flatMap.mp (hi.verticesActive p.2 hp0.2.1)
    obtain ⟨trees1, Lr, depth1, _, hi1, hact1, _, _, _, _, _, _, hfpR0, hfpR1, _, _, _, _, _, _⟩ :=
      lctReroot_spec pathPayload_laws hi htu huMem (by unfold isVertex vid; omega)
    have hv1 : vid p.2 ∈ trees1.flatMap AuxTree.toList := hact1.symm.mem_iff.mp (hi.verticesActive p.2 hp0.2.1)
    obtain ⟨tv1, htv1, hv1Mem⟩ := List.mem_flatMap.mp hv1
    obtain ⟨trees2, Lv, _, hi2, _, _, hfp2, _, _, _, _, _, _, _, _⟩ :=
      lctExpose_spec pathPayload_laws hi1 htv1 hv1Mem
    obtain ⟨treesA, La, depthA, _, hiA, _, _, _, _, _, _, hfpA, hfpExpA, _, _, _, _, _⟩ :=
      lctPathApply_spec pathPayload_laws hi htu huMem (by unfold isVertex vid; omega)
        htv hvMem hsubEq tag
    have hrr : lctReroot pathPayload s (vid p.1) = (lctRerootCost pathPayload s (vid p.1)).1 := rfl
    have hex : lctExpose pathPayload (lctRerootCost pathPayload s (vid p.1)).1 (vid p.2) =
        (lctExposeCost pathPayload (lctRerootCost pathPayload s (vid p.1)).1 (vid p.2)).1 := rfl
    have hs2n : (lctExposeCost pathPayload (lctRerootCost pathPayload s (vid p.1)).1 (vid p.2)).1.n = s.n :=
      (lctExposeCost_n _ _).trans (lctRerootCost_n _ _)
    have hsAn : (lctPathApplyCost pathPayload s (vid p.1) (vid p.2) tag).1.n =
        (lctExposeCost pathPayload (lctRerootCost pathPayload s (vid p.1)).1 (vid p.2)).1.n :=
      (lctPathApplyCost_n _ _ _ _).trans hs2n.symm
    obtain ⟨hmem_2, hmem_1, hpar2_eq⟩ := lctPathApply_same_trees_and_par hi2 hiA hsAn
      (lctPathApply_splay_eq s (vid p.1) (vid p.2) tag)
    -- Transfer `TreeEditNamedSlots` across one `lctPathApply` step
    obtain ⟨tsR, dsR, htsR, hpermR, harcR⟩ := treeEdit_reroot_edge_endpoints hi hp0.1
    obtain ⟨hpermR2, hparR2⟩ := treeEdit_witness_agreement htsR (hrr ▸ hi1)
    have hactR : (trees1.flatMap AuxTree.toList).Perm (trees.flatMap AuxTree.toList) :=
      hpermR2.symm.trans hpermR
    have hns1 : TreeEditNamedSlots (lctRerootCost pathPayload s (vid p.1)).1 trees1 F slot name := by
      have h1 : TreeEditNamedSlots (lctReroot pathPayload s (vid p.1)) trees1 F slot name := by
        refine ⟨fun e he => ?_, fun k hk hks => hn.inverse k (hactR.mem_iff.mp hk) hks, fun e he => ?_⟩
        · obtain ⟨ha, hb, hc⟩ := hn.forward e he; exact ⟨hactR.mem_iff.mpr ha, hb, hc⟩
        · have htV : isVertex s.n (vid (F.tail e)) := by unfold isVertex vid; have := (hV e he).1; omega
          have hhV : isVertex s.n (vid (F.head e)) := by unfold isVertex vid; have := (hV e he).2; omega
          rcases hn.endpoints e he with ⟨ha, hb⟩ | ⟨ha, hb⟩
          · have h := harcR (slot e) (hn.forward e he).1 (hn.forward e he).2.1 _ _ htV hhV ha hb
            rw [hparR2] at h; exact h
          · have h := harcR (slot e) (hn.forward e he).1 (hn.forward e he).2.1 _ _ hhV htV ha hb
            rw [hparR2] at h; exact h.symm
      rw [hrr] at h1; exact h1
    have hns2 : TreeEditNamedSlots (lctExposeCost pathPayload (lctRerootCost pathPayload s (vid p.1)).1 (vid p.2)).1
        trees2 F slot name := by
      have h := treeEditNamedSlots_expose_witness hns1 hi1 hv1 (hex ▸ hi2)
      rw [hex] at h; exact h
    have hactA2 : (treesA.flatMap AuxTree.toList).Perm (trees2.flatMap AuxTree.toList) := by
      refine (List.perm_ext_iff_of_nodup hiA.activeNodup hi2.activeNodup).mpr fun x => ?_
      constructor <;> intro hx
      · obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx; exact List.mem_flatMap.mpr ⟨t, hmem_1 t ht, hxt⟩
      · obtain ⟨t, ht, hxt⟩ := List.mem_flatMap.mp hx; exact List.mem_flatMap.mpr ⟨t, hmem_2 t ht, hxt⟩
    have hnsA : TreeEditNamedSlots (lctPathApply pathPayload s (vid p.1) (vid p.2) tag) treesA F slot name := by
      rw [lctPathApply_eq_cost]
      refine ⟨fun e he => ?_, fun k hk hks => hns2.inverse k (hactA2.mem_iff.mp hk) (hsAn ▸ hks), fun e he => ?_⟩
      · obtain ⟨ha, hb, hc⟩ := hns2.forward e he; exact ⟨hactA2.mem_iff.mpr ha, hsAn.symm ▸ hb, hc⟩
      · have he2 := hns2.endpoints e he; dsimp only at he2 ⊢; rw [hpar2_eq]; exact he2
    have hiA' : LctInvWith pathPayload (lctPathApply pathPayload s (vid p.1) (vid p.2) tag) treesA free depthA := by
      rw [lctPathApply_eq_cost]; exact hiA
    have hs1n : (lctPathApply pathPayload s (vid p.1) (vid p.2) tag).n = s.n := rfl
    obtain ⟨val1, hv1'⟩ := ih hiA' hnsA (hs1n.symm ▸ hV) (fun q hq => hpaths q (List.mem_cons_of_mem _ hq)) hi' sl val' hp'
    rw [lctPathApply_eq_cost] at hv1'
    exact lctPathApply_some_back_core hsAn (lctPathApply_splay_eq s (vid p.1) (vid p.2) tag)
      hfpR0 hfpR1 hi2 hfp2 hiA hfpA hfpExpA hiA hv1'

end MinCostFlow.MinRatio
