module

public import MinCostFlow.LSF.Program.T0Index
public import MinCostFlow.LSF.Program.RootTree
import Mathlib.Tactic.Linarith

/-!
# The rooted arrays describe `(T₀, r₀)`

`rootTreeProc` (`RootTree.lean`) writes, for each vertex index `x`, a parent index, a parent
edge index and a depth (`RTRooted`). Here we show that these are the parent, the parent edge and
the depth of `T₀` rooted at `r₀`, as the model defines them (`parent`, `parentEdge`, `depth` of
`TreeOps.lean`).

The idea: following the parent arrays from `x` gives a walk to the root whose depths go down by
one at each step, so its vertices are distinct and it is a path. In a forest the path between
two vertices is unique (`forestPath_eq_of_isPath`), so this path is `T₀[x, r₀]`, whose first
step gives the parent and the parent edge and whose length is the depth (`t0Rooted_spec`).
-/

namespace MinCostFlow.LSF.Program

open WordRAM MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- The rooted arrays `par`, `pe`, `dep` over vertex indices `x < n` with root index `r`:
the root is its own parent at depth `0`, and every other index has a parent joined to it by the
array edge `pe x`, one level up. This is `RTRooted` read as functions. -/
structure RootedArrays (n tM r : ℕ) (tl hd par pe dep : ℕ → ℕ) : Prop where
  par_r : par r = r
  dep_r : dep r = 0
  par_lt : ∀ x < n, par x < n
  step : ∀ x < n, x ≠ r →
    pe x < tM ∧ RTJoin tl hd (pe x) x (par x) ∧ dep x = dep (par x) + 1

lemma rootedArrays_of_rtRooted {n m r outPtr : ℕ} {tl hd : ℕ → ℕ} {mem : ℕ → ℕ}
    (h : RTRooted n m r outPtr tl hd mem) :
    RootedArrays n m r tl hd (fun x => mem (outPtr + x)) (fun x => mem (outPtr + n + x))
      (fun x => mem (outPtr + n + n + x)) :=
  ⟨h.1, h.2.1, fun x hx => (h.2.2 x hx).1, fun x hx hxr => (h.2.2 x hx).2.2 hxr⟩

/-- The walk from `x` to the root along the parent arrays is a path of length `dep x` whose
vertices all have depth at most `dep x`; when `x ≠ r` it starts with the parent edge. -/
private lemma rooted_path {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ}
    {fid tl hd par pe dep : ℕ → ℕ}
    (hA : T0IndexArrays T₀ vList tM fid tl hd) (hnd : vList.Nodup)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length) :
    ∀ d, ∀ x < vList.length, dep x = d →
      ∃ P, T₀.IsPath (vList.getD x 0) (vList.getD r 0) P ∧ P.length = d ∧
        (∀ y ∈ T₀.walkVertices (vList.getD x 0) P,
          ∃ z < vList.length, vList.getD z 0 = y ∧ dep z ≤ d) ∧
        (x ≠ r → ∃ b, P.head? = some (fid (pe x), b) ∧
          T₀.dst (fid (pe x), b) = vList.getD (par x) 0) ∧
        T₀.walkVertices (vList.getD x 0) P =
          (List.range (d + 1)).map (fun k => vList.getD (par^[k] x) 0) := by
  intro d
  induction d with
  | zero =>
    intro x hx hd0
    have hxr : x = r := by
      by_contra hne
      have := (hR.step x hx hne).2.2
      omega
    subst hxr
    refine ⟨[], ⟨MGraph.IsWalk.nil _, by simp [MGraph.walkVertices]⟩, rfl, ?_, fun h => absurd rfl h,
      by simp [MGraph.walkVertices]⟩
    intro y hy
    simp only [MGraph.walkVertices, List.map_nil, List.mem_singleton] at hy
    exact ⟨x, hx, hy.symm, by omega⟩
  | succ d ih =>
    intro x hx hdx
    have hxr : x ≠ r := by
      intro h; subst h; rw [hR.dep_r] at hdx; omega
    obtain ⟨hpe, hjoin, hdep⟩ := hR.step x hx hxr
    have hpx := hR.par_lt x hx
    obtain ⟨P, hP, hPlen, hPv, -, hPw⟩ := ih (par x) hpx (by omega)
    have hfE := hA.fid_mem _ hpe
    have htl := hA.tail_eq _ hpe
    have hhd := hA.head_eq _ hpe
    -- the first step, oriented from `x` to its parent
    obtain ⟨b, hsrc, hdst⟩ : ∃ b, T₀.src (fid (pe x), b) = vList.getD x 0 ∧
        T₀.dst (fid (pe x), b) = vList.getD (par x) 0 := by
      rcases hjoin with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨true, by simp [MGraph.src, htl, h1], by simp [MGraph.dst, hhd, h2]⟩
      · exact ⟨false, by simp [MGraph.src, hhd, h2], by simp [MGraph.dst, htl, h1]⟩
    have hwv0 : T₀.walkVertices (vList.getD x 0) ((fid (pe x), b) :: P) =
        vList.getD x 0 :: T₀.walkVertices (vList.getD (par x) 0) P := by
      simp [MGraph.walkVertices, hdst]
    refine ⟨(fid (pe x), b) :: P, ⟨MGraph.IsWalk.cons hfE hsrc (hdst ▸ hP.1), ?_⟩, by simp [hPlen],
      ?_, fun _ => ⟨b, rfl, hdst⟩, ?_⟩
    rotate_right
    · rw [hwv0, hPw, List.range_succ_eq_map (n := d + 1)]
      simp [List.map_map, Function.comp_def, Function.iterate_succ_apply]
    · -- the vertices are distinct: `x` has depth `d + 1`, the others at most `d`
      have hwv : T₀.walkVertices (vList.getD x 0) ((fid (pe x), b) :: P) =
          vList.getD x 0 :: T₀.walkVertices (vList.getD (par x) 0) P := by
        simp [MGraph.walkVertices, hdst]
      rw [hwv, List.nodup_cons]
      refine ⟨fun hmem => ?_, hP.2⟩
      obtain ⟨z, hz, hzv, hzd⟩ := hPv _ hmem
      have hzx : z = x := by
        rw [List.getD_eq_getElem _ _ hz, List.getD_eq_getElem _ _ hx] at hzv
        exact (hnd.getElem_inj_iff).mp hzv
      subst hzx
      omega
    · intro y hy
      have hwv : T₀.walkVertices (vList.getD x 0) ((fid (pe x), b) :: P) =
          vList.getD x 0 :: T₀.walkVertices (vList.getD (par x) 0) P := by
        simp [MGraph.walkVertices, hdst]
      rw [hwv, List.mem_cons] at hy
      rcases hy with rfl | hy
      · exact ⟨x, hx, rfl, by omega⟩
      · obtain ⟨z, hz, hzv, hzd⟩ := hPv y hy
        exact ⟨z, hz, hzv, by omega⟩

/-- The rooted arrays give the parent, the parent edge and the depth of `(T₀, r₀)`. -/
theorem t0Rooted_spec {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ}
    {fid tl hd par pe dep : ℕ → ℕ}
    (hT : T₀.IsForest) (hA : T0IndexArrays T₀ vList tM fid tl hd) (hnd : vList.Nodup)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    {x : ℕ} (hx : x < vList.length) :
    depth T₀ (vList.getD r 0) (vList.getD x 0) = dep x ∧
    (x ≠ r → parent T₀ (vList.getD r 0) (vList.getD x 0) = vList.getD (par x) 0 ∧
      parentEdge T₀ (vList.getD r 0) (vList.getD x 0) = fid (pe x)) := by
  obtain ⟨P, hP, hPlen, -, hhead, -⟩ := rooted_path hA hnd hR hr (dep x) x hx rfl
  have hfp := forestPath_eq_of_isPath hT hP
  refine ⟨by rw [depth, hfp, hPlen], fun hxr => ?_⟩
  obtain ⟨b, hb, hdst⟩ := hhead hxr
  obtain ⟨y, P', rfl⟩ : ∃ y P', P = y :: P' := by
    cases P with
    | nil => simp at hb
    | cons y P' => exact ⟨y, P', rfl⟩
  simp only [List.head?_cons, Option.some.injEq] at hb
  subst hb
  refine ⟨?_, ?_⟩
  · rw [parent, hfp]; exact hdst
  · rw [parentEdge, hfp]

/-- Ancestors in `(T₀, r₀)` are the iterated parents in the arrays. -/
theorem t0Rooted_isAncestor_iff {T₀ : MGraph} {vList : List ℕ} {tM r : ℕ}
    {fid tl hd par pe dep : ℕ → ℕ}
    (hT : T₀.IsForest) (hA : T0IndexArrays T₀ vList tM fid tl hd) (hnd : vList.Nodup)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length)
    {x z : ℕ} (hx : x < vList.length) (hz : z < vList.length) :
    IsAncestor T₀ (vList.getD r 0) (vList.getD z 0) (vList.getD x 0) ↔
      ∃ k ≤ dep x, par^[k] x = z := by
  obtain ⟨P, hP, -, -, -, hPw⟩ := rooted_path hA hnd hR hr (dep x) x hx rfl
  have hfp := forestPath_eq_of_isPath hT hP
  have hit : ∀ k, par^[k] x < vList.length := by
    intro k
    induction k with
    | zero => exact hx
    | succ k ih => rw [Function.iterate_succ_apply']; exact hR.par_lt _ ih
  rw [IsAncestor, hfp, hPw, List.mem_map]
  constructor
  · rintro ⟨k, hk, hkz⟩
    rw [List.getD_eq_getElem _ _ (hit k), List.getD_eq_getElem _ _ hz] at hkz
    exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, (hnd.getElem_inj_iff).mp hkz⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, by simpa [Nat.lt_succ_iff] using hk, rfl⟩

end

end MinCostFlow.LSF.Program
