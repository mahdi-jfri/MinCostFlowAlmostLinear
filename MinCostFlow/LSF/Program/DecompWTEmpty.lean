module

public import MinCostFlow.LSF.Program.DecompWT

/-!
# The decomposition `W_T` when `G₀` has no edges

`wT_spec` needs an edge of `G₀`, since the threshold `θ` of the model divides by the number of
edges. When `G₀` has no edges, every vertex has weight `0`, so the five passes do little: the
greedy pass never closes a batch, every label is `(r, 0)`, no vertex is marked, and the closure
pass puts no vertex in the boundary. `wT_spec_empty` shows that the one-piece decomposition
`{T₀.V}` then has the three facts of `wT_spec`. Lemma B.7 holds for it by
`isTreeDecompSpec_zero`.

The induction runs along the top-down order `Q` of the passes: a parent comes before each of
its children (`idx_par_lt`), so facts that go up the tree follow by induction from the end of `Q`
(`topDown_up`), and facts that go down follow from its start (`topDown_down`).
-/

namespace MinCostFlow.LSF.Program

@[expose] public section

open MinCostFlow MinCostFlow.LSF MinCostFlow.LSF.Program.DecompGen

variable {n r : ℕ} {par : ℕ → ℕ} {Q : List ℕ}

/-- In a top-down order, a parent comes before its child. -/
lemma idx_par_lt (hQ : TopDownOrder n r par Q) {c : ℕ} (hc : c < n) (hcr : c ≠ r) :
    Q.idxOf (par c) < Q.idxOf c := by
  have hcQ := hQ.cover c hc
  have hj : Q.idxOf c < Q.length := List.idxOf_lt_length_of_mem hcQ
  have hQj : Q[Q.idxOf c] = c := List.getElem_idxOf hj
  have hmem := hQ.after (Q.idxOf c) hj (by rw [hQj]; exact hcr)
  rw [hQj] at hmem
  obtain ⟨i, hi, hik⟩ := List.getElem_of_mem hmem
  rw [List.length_take] at hi
  rw [List.getElem_take] at hik
  rw [← hik, hQ.nodup.idxOf_getElem i (by omega)]
  omega

/-- Induction from the leaves up: a fact that holds at `u` once it holds at the children of `u`
holds everywhere. -/
lemma topDown_up (hQ : TopDownOrder n r par Q) {P : ℕ → Prop}
    (h : ∀ u < n, (∀ c < n, c ≠ r → par c = u → P c) → P u) : ∀ u < n, P u := by
  have key : ∀ d, ∀ u < n, n - Q.idxOf u ≤ d → P u := by
    intro d
    induction d with
    | zero =>
      intro u hu hd
      have := List.idxOf_lt_length_of_mem (hQ.cover u hu)
      rw [hQ.len] at this
      omega
    | succ d ih =>
      intro u hu hd
      refine h u hu fun c hc hcr hpc => ih c hc ?_
      have := idx_par_lt hQ hc hcr
      rw [hpc] at this
      omega
  exact fun u hu => key n u hu (Nat.sub_le _ _)

/-- Induction from the root down. -/
lemma topDown_down (hQ : TopDownOrder n r par Q) (hpar : ∀ x < n, par x < n) {P : ℕ → Prop}
    (h0 : P r) (h : ∀ x < n, x ≠ r → P (par x) → P x) : ∀ x < n, P x := by
  have key : ∀ d, ∀ x < n, Q.idxOf x ≤ d → P x := by
    intro d
    induction d with
    | zero =>
      intro x hx hd
      by_cases hxr : x = r
      · rw [hxr]; exact h0
      · have := idx_par_lt hQ hx hxr; omega
    | succ d ih =>
      intro x hx hd
      by_cases hxr : x = r
      · rw [hxr]; exact h0
      · exact h x hx hxr (ih (par x) (hpar x hx) (by have := idx_par_lt hQ hx hxr; omega))
  exact fun x hx => key _ x hx le_rfl

/-- The positions after the first are the vertices other than the root. -/
lemma mem_drop_one (hQ : TopDownOrder n r par Q) (hn : 0 < n) {x : ℕ} :
    x ∈ Q.drop 1 ↔ x < n ∧ x ≠ r := by
  have hlen : 0 < Q.length := by rw [hQ.len]; exact hn
  have h0 := hQ.head_eq hn
  obtain ⟨a, l, hQl⟩ : ∃ a l, Q = a :: l := by
    cases hq : Q with
    | nil => rw [hq] at hlen; simp at hlen
    | cons a l => exact ⟨a, l, rfl⟩
  subst hQl
  have har : a = r := h0
  subst har
  have hnd := List.nodup_cons.mp hQ.nodup
  simp only [List.drop_succ_cons, List.drop_zero]
  constructor
  · intro hx
    exact ⟨hQ.lt x (List.mem_cons_of_mem _ hx), fun h => hnd.1 (h ▸ hx)⟩
  · rintro ⟨hx, hxr⟩
    rcases List.mem_cons.mp (hQ.cover x hx) with h | h
    · exact absurd h hxr
    · exact h

/-- An online run over weights `0` with a positive threshold never closes a batch. -/
lemma onlineRun_zero {α : Type*} {θ : ℝ} (hθ : 0 < θ) {f : α → ℝ} {b : α → ℕ} :
    ∀ (xs : List α) (nb nbF : ℕ) (curF : ℝ), (∀ x ∈ xs, f x = 0) →
      OnlineRun θ f b nb 0 xs nbF curF → nbF = nb ∧ curF = 0 ∧ ∀ x ∈ xs, b x = nb := by
  intro xs
  induction xs with
  | nil =>
    intro nb nbF curF _ h
    exact ⟨h.1, h.2, fun _ hx => absurd hx (List.not_mem_nil)⟩
  | cons x xs ih =>
    intro nb nbF curF hf h
    obtain ⟨hbx, hrest⟩ := h
    have hfx : f x = 0 := hf x (List.mem_cons_self)
    rw [hfx, zero_add, if_neg (not_le.mpr hθ)] at hrest
    obtain ⟨h1, h2, h3⟩ := ih nb nbF curF (fun y hy => hf y (List.mem_cons_of_mem _ hy)) hrest
    refine ⟨h1, h2, fun y hy => ?_⟩
    rcases List.mem_cons.mp hy with rfl | hy
    · exact hbx
    · exact h3 y hy

open Classical in
/-- `wT_spec` when `G₀` has no edges: the one-piece decomposition `{T₀.V}` has the three facts. -/
theorem wT_spec_empty {G₀ T₀ : MGraph} {vList : List ℕ} {tM r k : ℕ}
    {fid tl hd par pe dep : ℕ → ℕ} {Q : List ℕ}
    {deg ν cur nb bidx s labY labB S cnt has inR : ℕ → ℕ}
    (hE0 : G₀.E = ∅) (hk : 0 < k)
    (hT : IsRootedTree T₀ (vList.getD r 0)) (_hA : T0IndexArrays T₀ vList tM fid tl hd)
    (hnd : vList.Nodup) (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    (hQ : TopDownOrder vList.length r par Q)
    (hdeg : ∀ x < vList.length, (deg x : ℝ) = vWeight G₀ (fun _ => 1) (vList.getD x 0))
    (hν : ∀ x < vList.length, ν x = degNu (decompThetaNat G₀ k) (deg x))
    (hG : GreedyState Q par vList.length (decompThetaNat G₀ k) ν cur nb bidx s 1)
    (hlab : ∀ x < vList.length, x ≠ r → LabelRule par nb bidx labY labB r x)
    (hS : ∀ x < vList.length, x ≠ r → S x = markVal (decompThetaNat G₀ k) (nb x) (deg x))
    (hSr : S r = rootMarkVal (decompThetaNat G₀ k) (nb r) (deg r)
      (rootFlag par bidx nb r vList.length))
    (hC : ClosureState Q par vList.length S cnt has inR 1)
    (hCr : inR r = closureIn (S r) (cnt r)) :
    ∃ W : Finset (Finset ℕ), IsTreeDecompSpec G₀ T₀ k W ∧
    (∀ v ∈ T₀.V, vtxFun vList inR v = 1 ↔ v ∈ boundary W) ∧
    (∀ x < vList.length, x ≠ r → ∀ x' < vList.length, x' ≠ r →
      ((labY x = labY x' ∧ labB x = labB x') ↔ ∃ P ∈ W,
        parentEdge T₀ (vList.getD r 0) (vList.getD x 0) ∈ inducedEdges T₀ P ∧
        parentEdge T₀ (vList.getD r 0) (vList.getD x' 0) ∈ inducedEdges T₀ P)) := by
  set n := vList.length with hn_def
  have hn : 0 < n := by omega
  have hθ : 0 < decompThetaNat G₀ k := by
    unfold decompThetaNat; positivity
  have hθR : (0 : ℝ) < (decompThetaNat G₀ k : ℝ) := by exact_mod_cast hθ
  have hdrop : ∀ {x}, x ∈ Q.drop 1 ↔ x < n ∧ x ≠ r := mem_drop_one hQ hn
  -- every degree is zero, so every weight `ν` is zero
  have hdeg0 : ∀ x < n, deg x = 0 := fun x hx => by
    have h := hdeg x hx
    simp only [vWeight, hE0, Finset.sum_empty] at h
    exact_mod_cast h
  have hν0 : ∀ x < n, ν x = 0 := fun x hx => by
    rw [hν x hx, hdeg0 x hx]; simp [degNu]
  -- the children of `u` in the greedy pass are its children among the indices
  have hpc : ∀ u c, c ∈ procChildren Q par u 1 ↔ (c < n ∧ c ≠ r) ∧ par c = u := by
    intro u c
    simp only [procChildren, List.mem_filter, List.mem_reverse, decide_eq_true_eq, hdrop]
  -- the greedy pass: every `cur` is zero
  have hcur : ∀ u < n, cur u = 0 := by
    refine topDown_up hQ fun u hu ih => ?_
    have hrun := hG.1 u hu
    have h := onlineRun_zero hθR (procChildren Q par u 1) 0 (nb u) (cur u : ℝ) (fun c hc => by
      obtain ⟨⟨hcn, hcr⟩, hcu⟩ := (hpc u c).mp hc
      show ((s c : ℕ) : ℝ) = 0
      rw [hG.2.1 c (hdrop.mpr ⟨hcn, hcr⟩), hν0 c hcn, ih c hcn hcr hcu]; simp) hrun
    exact_mod_cast h.2.1
  have hgr : ∀ u < n, nb u = 0 ∧ ∀ c ∈ procChildren Q par u 1, bidx c = 0 := by
    intro u hu
    have h := onlineRun_zero hθR (procChildren Q par u 1) 0 (nb u) (cur u : ℝ) (fun c hc => by
      obtain ⟨⟨hcn, hcr⟩, -⟩ := (hpc u c).mp hc
      show ((s c : ℕ) : ℝ) = 0
      rw [hG.2.1 c (hdrop.mpr ⟨hcn, hcr⟩), hν0 c hcn, hcur c hcn]; simp) (hG.1 u hu)
    exact ⟨h.1, h.2.2⟩
  have hnb : ∀ u < n, nb u = 0 := fun u hu => (hgr u hu).1
  have hbidx : ∀ x < n, x ≠ r → bidx x = 0 := fun x hx hxr =>
    (hgr (par x) (hR.par_lt x hx)).2 x ((hpc _ x).mpr ⟨⟨hx, hxr⟩, rfl⟩)
  -- the labels: every vertex other than the root has label `(r, 0)`
  have hlab0 : ∀ x < n, x ≠ r → labY x = r ∧ labB x = 0 := by
    refine topDown_down hQ hR.par_lt (fun h => absurd rfl h) fun x hx hxr ih _ => ?_
    have h := hlab x hx hxr
    unfold LabelRule at h
    rw [hbidx x hx hxr, hnb (par x) (hR.par_lt x hx)] at h
    by_cases hpr : par x = r
    · rw [if_pos (Or.inr hpr), Prod.mk.injEq] at h
      exact ⟨h.1.trans hpr, h.2⟩
    · rw [if_neg (by omega), Prod.mk.injEq] at h
      obtain ⟨h1, h2⟩ := ih hpr
      exact ⟨h.1.trans h1, h.2.trans h2⟩
  -- the marks are zero
  have hS0 : ∀ x < n, S x = 0 := by
    intro x hx
    by_cases hxr : x = r
    · rw [hxr, hSr, hnb r hr, hdeg0 r hr]; simp [rootMarkVal]
    · rw [hS x hx hxr, hnb x hx, hdeg0 x hx]; simp [markVal]
  -- the closure pass: nothing is collected, so nothing is in the boundary
  have hhas : ∀ u < n, u ≠ r → has u = 0 := by
    refine topDown_up hQ fun u hu ih hur => ?_
    have hcnt : cnt u = 0 := by
      rw [hC.1 u hu, List.length_eq_zero_iff, List.filter_eq_nil_iff]
      intro c hc
      obtain ⟨hcn, hcr⟩ := hdrop.mp hc
      simp only [decide_eq_true_eq, not_and]
      intro hcu
      rw [ih c hcn hcr hcu hcr]; omega
    rw [(hC.2 u (hdrop.mpr ⟨hu, hur⟩)).1, hS0 u hu, hcnt]; rfl
  have hcnt0 : ∀ u < n, cnt u = 0 := by
    intro u hu
    rw [hC.1 u hu, List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro c hc
    obtain ⟨hcn, hcr⟩ := hdrop.mp hc
    simp only [decide_eq_true_eq, not_and]
    intro _
    rw [hhas c hcn hcr]; omega
  have hinR : ∀ x < n, inR x = 0 := by
    intro x hx
    by_cases hxr : x = r
    · rw [hxr, hCr, hS0 r hr, hcnt0 r hr]; rfl
    · rw [(hC.2 x (hdrop.mpr ⟨hx, hxr⟩)).2, hS0 x hx, hcnt0 x hx]; rfl
  -- the one-piece decomposition
  have hbnd : boundary ({T₀.V} : Finset (Finset ℕ)) = ∅ := by
    ext v
    simp only [mem_boundary_iff, Finset.mem_singleton, Finset.notMem_empty, iff_false]
    rintro ⟨W₁, rfl, W₂, rfl, hne, -⟩
    exact hne rfl
  refine ⟨{T₀.V}, isTreeDecompSpec_zero hT hE0 (by exact_mod_cast hk), fun v hv => ?_,
    fun x hx hxr x' hx' hx'r => ?_⟩
  · rw [hbnd]
    have hi : vList.idxOf v < n := List.idxOf_lt_length_of_mem ((hV v).mp hv)
    simp only [vtxFun, hinR _ hi, Finset.notMem_empty, iff_false]
    omega
  · have hmem : ∀ y < n, y ≠ r →
        parentEdge T₀ (vList.getD r 0) (vList.getD y 0) ∈ inducedEdges T₀ T₀.V := by
      intro y hy hyr
      have hyV : vList.getD y 0 ∈ T₀.V := by
        rw [hV, List.getD_eq_getElem _ _ hy]; exact List.getElem_mem _
      have hne : vList.getD y 0 ≠ vList.getD r 0 := fun h => hyr (getD_inj hnd hy hr h)
      have he := parentEdge_mem hT hyV hne
      exact Finset.mem_filter.mpr ⟨he, hT.isForest.1 _ he⟩
    obtain ⟨a1, a2⟩ := hlab0 x hx hxr
    obtain ⟨b1, b2⟩ := hlab0 x' hx' hx'r
    exact iff_of_true ⟨a1.trans b1.symm, a2.trans b2.symm⟩
      ⟨T₀.V, Finset.mem_singleton_self _, hmem x hx hxr, hmem x' hx' hx'r⟩

end

end MinCostFlow.LSF.Program
