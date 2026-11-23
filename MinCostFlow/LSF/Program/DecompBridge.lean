module

public import MinCostFlow.LSF.Program.DecompGreedyMath
public import MinCostFlow.LSF.Program.DecompGenLabel
public import MinCostFlow.LSF.Program.T0Rooted

/-!
# From the index arrays to the tree `T₀`

The greedy pass works on vertex indices `x < n`, the positions in `vList`. The results about
`progDecomp` are about the vertices of `T₀`. This file moves the result of the pass to the
vertices: the vertex `u = vList[i]` gets the numbers of the index `i` (`vtxFun`), and its child
list is the list of the children of `i` in the order of the walk, read as vertices
(`greedyChildLists`). `greedy_bridge` shows that these are child lists of `(T₀, r₀)` and that
every vertex was handled as `OnlineRun` says, which is what `progDecomp_char` asks for.
-/

@[expose] public section

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program.DecompGen

/-- A function on indices, read on vertices. -/
def vtxFun (vList : List ℕ) (f : ℕ → ℕ) (v : ℕ) : ℕ := f (vList.idxOf v)

/-- The child lists of the greedy pass, as vertices. -/
def greedyChildLists (vList Q : List ℕ) (par : ℕ → ℕ) (u : ℕ) : List ℕ :=
  (procChildren Q par (vList.idxOf u) 1).map (fun x => vList.getD x 0)

lemma idxOf_getD {vList : List ℕ} (hnd : vList.Nodup) {x : ℕ} (hx : x < vList.length) :
    vList.idxOf (vList.getD x 0) = x := by
  rw [List.getD_eq_getElem _ _ hx]
  exact hnd.idxOf_getElem x hx

lemma getD_idxOf {vList : List ℕ} {v : ℕ} (hv : v ∈ vList) :
    vList.getD (vList.idxOf v) 0 = v := by
  rw [List.getD_eq_getElem _ _ (List.idxOf_lt_length_of_mem hv)]
  exact List.getElem_idxOf (List.idxOf_lt_length_of_mem hv)

lemma getD_inj {vList : List ℕ} (hnd : vList.Nodup) {a b : ℕ} (ha : a < vList.length)
    (hb : b < vList.length) (h : vList.getD a 0 = vList.getD b 0) : a = b := by
  rw [List.getD_eq_getElem _ _ ha, List.getD_eq_getElem _ _ hb] at h
  exact (hnd.getElem_inj_iff).mp h

lemma mem_childSet_iff {T : MGraph} {r u c : ℕ} (hT : IsRootedTree T r) :
    c ∈ childSet T r u ↔ c ∈ T.V ∧ c ≠ r ∧ parent T r c = u := by
  constructor
  · intro hc
    obtain ⟨hcV, hcr, hp, -⟩ := childSet_facts hT hc
    exact ⟨hcV, hcr, hp⟩
  · rintro ⟨hcV, hcr, rfl⟩
    exact mem_childSet_parent hT hcV hcr

lemma TopDownOrder.mem_drop_one {n r : ℕ} {par : ℕ → ℕ} {Q : List ℕ}
    (hQ : TopDownOrder n r par Q) (hn : 0 < n) {x : ℕ} :
    x ∈ Q.drop 1 ↔ x < n ∧ x ≠ r := by
  have hQ0 := hQ.head_eq hn
  have hlen : 0 < Q.length := by rw [hQ.len]; exact hn
  have hQe : Q = Q[0] :: Q.drop 1 := by
    conv_lhs => rw [← List.take_append_drop 1 Q]
    rw [List.take_one, List.head?_eq_getElem? , List.getElem?_eq_getElem hlen]
    rfl
  have hnd := hQ.nodup
  rw [hQe, List.nodup_cons, hQ0] at hnd
  constructor
  · intro hx
    refine ⟨hQ.lt x (List.mem_of_mem_drop hx), fun h => hnd.1 (h ▸ hx)⟩
  · rintro ⟨hxn, hxr⟩
    have hxQ := hQ.cover x hxn
    rw [hQe, hQ0, List.mem_cons] at hxQ
    exact hxQ.resolve_left hxr

lemma onlineRun_map {α β : Type*} {θ : ℝ} {f : β → ℝ} {b : β → ℕ} (g : α → β) :
    ∀ (xs : List α) (nb : ℕ) (cur : ℝ) (nbF : ℕ) (curF : ℝ),
      OnlineRun θ (f ∘ g) (b ∘ g) nb cur xs nbF curF → OnlineRun θ f b nb cur (xs.map g) nbF curF := by
  intro xs
  induction xs with
  | nil => intro nb cur nbF curF h; exact h
  | cons x xs ih =>
    intro nb cur nbF curF h
    obtain ⟨hx, h⟩ := h
    refine ⟨hx, ?_⟩
    simp only [Function.comp] at h
    split_ifs at h ⊢ <;> exact ih _ _ _ _ h

/-- The greedy pass gives child lists of `(T₀, r₀)`, and every vertex was handled as `OnlineRun`
says. The weights are `νR` on vertices, given on indices by `ν`. -/
theorem greedy_bridge {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ}
    {fid tl hd par pe dep : ℕ → ℕ} {Q : List ℕ} {θ : ℕ} {ν cur nb bidx s : ℕ → ℕ}
    (hT : IsRootedTree T₀ (vList.getD r 0)) (hA : T0IndexArrays T₀ vList tM fid tl hd)
    (hnd : vList.Nodup) (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    (hQ : TopDownOrder vList.length r par Q)
    (hG : GreedyState Q par vList.length θ ν cur nb bidx s 1)
    (νR : ℕ → ℝ) (hνR : ∀ x < vList.length, νR (vList.getD x 0) = (ν x : ℝ)) :
    IsChildLists T₀ (vList.getD r 0) (greedyChildLists vList Q par) ∧
    ∀ u ∈ T₀.V, OnlineRun (θ : ℝ) (fun v => νR v + (vtxFun vList cur v : ℝ))
      (vtxFun vList bidx) 0 0 (greedyChildLists vList Q par u) (vtxFun vList nb u)
      ((νR u + (vtxFun vList cur u : ℝ)) - νR u) := by
  classical
  set n := vList.length with hn_def
  have hn : 0 < n := by omega
  have hprocmem : ∀ i x, x ∈ procChildren Q par i 1 ↔ (x < n ∧ x ≠ r) ∧ par x = i := by
    intro i x
    unfold procChildren
    rw [List.mem_filter, List.mem_reverse, hQ.mem_drop_one hn, decide_eq_true_iff]
  have hparent : ∀ x < n, x ≠ r →
      parent T₀ (vList.getD r 0) (vList.getD x 0) = vList.getD (par x) 0 := fun x hx hxr =>
    ((t0Rooted_spec hT.isForest hA hnd hR hr hx).2 hxr).1
  refine ⟨fun u hu => ⟨?_, fun c => ?_⟩, fun u hu => ?_⟩
  · unfold greedyChildLists procChildren
    refine List.Nodup.map_on (fun x hx y hy hxy => ?_) ?_
    · have hx' := hQ.lt x (List.mem_of_mem_drop (List.mem_reverse.mp (List.mem_filter.mp hx).1))
      have hy' := hQ.lt y (List.mem_of_mem_drop (List.mem_reverse.mp (List.mem_filter.mp hy).1))
      exact getD_inj hnd hx' hy' hxy
    · exact (List.nodup_reverse.mpr ((hQ.nodup).sublist (List.drop_sublist _ _))).filter _
  · have huL : u ∈ vList := (hV u).mp hu
    have hiu := List.idxOf_lt_length_of_mem huL
    rw [mem_childSet_iff hT, greedyChildLists, List.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨⟨hxn, hxr⟩, hpx⟩ := (hprocmem _ x).mp hx
      refine ⟨(hV _).mpr (by rw [List.getD_eq_getElem _ _ hxn]; exact List.getElem_mem _),
        fun h => hxr (getD_inj hnd hxn hr h), ?_⟩
      rw [hparent x hxn hxr, hpx, getD_idxOf huL]
    · rintro ⟨hcV, hcr, hpc⟩
      have hcL : c ∈ vList := (hV c).mp hcV
      set x := vList.idxOf c with hx
      have hxn : x < n := List.idxOf_lt_length_of_mem hcL
      have hxc : vList.getD x 0 = c := getD_idxOf hcL
      have hxr : x ≠ r := fun h => hcr (by rw [← hxc, h])
      refine ⟨x, (hprocmem _ x).mpr ⟨⟨hxn, hxr⟩, ?_⟩, hxc⟩
      have h1 := hparent x hxn hxr
      rw [hxc, hpc, ← getD_idxOf huL] at h1
      exact (getD_inj hnd hiu (hR.par_lt x hxn) h1).symm
  · have huL : u ∈ vList := (hV u).mp hu
    have hiu := List.idxOf_lt_length_of_mem huL
    have hrun := hG.1 _ hiu
    have hcongr : ∀ x ∈ procChildren Q par (vList.idxOf u) 1,
        ((s x : ℕ) : ℝ) = ((fun v => νR v + (vtxFun vList cur v : ℝ)) ∘ (fun x => vList.getD x 0)) x ∧
        bidx x = (vtxFun vList bidx ∘ (fun x => vList.getD x 0)) x := by
      intro x hx
      obtain ⟨⟨hxn, hxr⟩, -⟩ := (hprocmem _ x).mp hx
      have hsx := hG.2.1 x ((hQ.mem_drop_one hn).mpr ⟨hxn, hxr⟩)
      simp only [Function.comp, vtxFun, idxOf_getD hnd hxn, hνR x hxn, hsx]
      constructor <;> (try trivial) <;> (try (push_cast; ring))
    have h2 := onlineRun_congr _ _ _ _ _ hcongr hrun
    have h3 := onlineRun_map (fun x => vList.getD x 0) _ _ _ _ _ h2
    rw [show (νR u + (vtxFun vList cur u : ℝ)) - νR u = (vtxFun vList cur u : ℝ) by ring]
    exact h3

end MinCostFlow.LSF.Program

end
