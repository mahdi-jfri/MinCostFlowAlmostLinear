module

public import MinCostFlow.LSF.Program.UpMin
public import MinCostFlow.LSF.Program.FRMath
public import MinCostFlow.LSF.Program.T0Rooted
public import MinCostFlow.LSF.Program.TreeArrays

/-!
# The jump table `liftMin` names the first edge of each jump

For the arrays of the rooted tree `(T₀, r₀)`, the edges on the way from vertex index `i` up `k`
steps are `upEdges i k`: the parent edges of `i`, `par i`, … until the root. `walkEdges_up_eq`
shows these are the edges of the tree path, and `upEdges_add` splits a long way up into two.

`liftMin_spec` then shows what `AuxAt` asks of `upMinIdx`: when the jump of `i` at level `j` moves,
`liftMin` (on the ancestor table `liftF par`) is a tree edge index on the jump that comes first in
the order `π` among the edges of the jump.
-/

namespace MinCostFlow.LSF.Program

open MinCostFlow MinCostFlow.LSF

@[expose] public section

/-- The edges on the way from index `i` up `k` steps, as tree edges. -/
def upEdges (fid par pe : ℕ → ℕ) (r : ℕ) : ℕ → ℕ → Finset ℕ
  | _, 0 => ∅
  | i, k + 1 => if i = r then ∅ else insert (fid (pe i)) (upEdges fid par pe r (par i) k)

variable {n tM r : ℕ} {fid tl hd par pe dep : ℕ → ℕ}

lemma upEdges_root (fid par pe : ℕ → ℕ) (r k : ℕ) : upEdges fid par pe r r k = ∅ := by
  cases k <;> simp [upEdges]

lemma upEdges_add (hR : RootedArrays n tM r tl hd par pe dep) (a : ℕ) :
    ∀ b i, upEdges fid par pe r i (a + b) =
      upEdges fid par pe r i a ∪ upEdges fid par pe r (par^[a] i) b := by
  induction a with
  | zero => intro b i; simp [upEdges]
  | succ a ih =>
    intro b i
    rw [show a + 1 + b = (a + b) + 1 by omega]
    by_cases hi : i = r
    · subst hi
      have hit : par^[a + 1] i = i := Function.iterate_fixed hR.par_r _
      rw [hit, upEdges_root, upEdges_root, upEdges_root, Finset.empty_union]
    · simp only [upEdges, hi, if_false]
      rw [ih b (par i), Function.iterate_succ_apply, Finset.insert_union]

/-- An index that comes back to itself after some steps up is the root. -/
lemma eq_r_of_iterate_eq (hR : RootedArrays n tM r tl hd par pe dep) {x k : ℕ} (hx : x < n)
    (hk : 1 ≤ k) (h : par^[k] x = x) : x = r := by
  by_contra hxr
  have h1 := hR.dep_iterate hx k
  have h2 := (hR.step x hx hxr).2.2
  rw [h] at h1
  omega

/-- The tree path from `vList[i]` up to its `k`-th ancestor has the edges `upEdges i k`. -/
theorem walkEdges_up_eq {T₀ : MGraph} {vList : List ℕ}
    (hT : IsRootedTree T₀ (vList.getD r 0)) (hA : T0IndexArrays T₀ vList tM fid tl hd)
    (hnd : vList.Nodup) (hV : ∀ v, v ∈ T₀.V ↔ v ∈ vList)
    (hR : RootedArrays vList.length tM r tl hd par pe dep) (hr : r < vList.length) (k : ℕ) :
    ∀ i < vList.length, walkEdges (T₀.forestPath (vList.getD i 0) (vList.getD (par^[k] i) 0)) =
      upEdges fid par pe r i k := by
  induction k with
  | zero =>
    intro i hi
    simp [upEdges, forestPath_self hT.isForest]
  | succ k ih =>
    intro i hi
    by_cases hir : i = r
    · subst hir
      rw [Function.iterate_fixed hR.par_r, forestPath_self hT.isForest, upEdges_root]
      rfl
    · have hpi := hR.par_lt i hi
      have hmemV : ∀ x < vList.length, vList.getD x 0 ∈ T₀.V := fun x hx =>
        (hV _).mpr (by rw [List.getD_eq_getElem _ _ hx]; exact List.getElem_mem _)
      have hz := hR.iterate_lt hi (k + 1)
      -- the target is an ancestor, different from the start
      have hanc : IsAncestor T₀ (vList.getD r 0) (vList.getD (par^[k + 1] i) 0)
          (vList.getD i 0) := by
        rw [t0Rooted_isAncestor_iff hT.isForest hA hnd hR hr hi hz]
        by_cases hk : k + 1 ≤ dep i
        · exact ⟨k + 1, hk, rfl⟩
        · refine ⟨dep i, le_rfl, ?_⟩
          rw [hR.iterate_dep hi le_rfl, hR.iterate_dep hi (by omega)]
      have hne : vList.getD (par^[k + 1] i) 0 ≠ vList.getD i 0 := by
        intro h
        rw [List.getD_eq_getElem _ _ hz, List.getD_eq_getElem _ _ hi] at h
        exact hir (eq_r_of_iterate_eq hR hi (by omega) ((hnd.getElem_inj_iff).mp h))
      obtain ⟨-, -, hstep, -⟩ := walkEdges_up_step hT (hmemV i hi) hanc hne
      obtain ⟨hpar, hpe⟩ := (t0Rooted_spec hT.isForest hA hnd hR hr hi).2 hir
      rw [hstep, hpar, hpe, Function.iterate_succ_apply, ih (par i) hpi]
      simp only [upEdges, hir, if_false]

/-- The edges of `upEdges i k` are parent edges of non-root indices on the way up. -/
lemma mem_upEdges (hR : RootedArrays n tM r tl hd par pe dep) (k : ℕ) :
    ∀ i < n, ∀ e ∈ upEdges fid par pe r i k, ∃ y < n, y ≠ r ∧ e = fid (pe y) := by
  induction k with
  | zero => intro i _ e he; simp [upEdges] at he
  | succ k ih =>
    intro i hi e he
    by_cases hir : i = r
    · simp [upEdges, hir] at he
    · simp only [upEdges, hir, if_false, Finset.mem_insert] at he
      rcases he with rfl | he
      · exact ⟨i, hi, hir, rfl⟩
      · exact ih (par i) (hR.par_lt i hi) e he

/-- The table `liftMin` on the ancestor table names the first edge (in the order `π`) of each
jump that moves. -/
theorem liftMin_spec (hR : RootedArrays n tM r tl hd par pe dep) {π piv : ℕ → ℕ}
    (hpiv : ∀ t < tM, piv t = π (fid t)) (j : ℕ) :
    ∀ i < n, liftF par i j ≠ i →
      liftMin (fun i j => liftF par i j) pe piv r i j < tM ∧
      fid (liftMin (fun i j => liftF par i j) pe piv r i j) ∈ upEdges fid par pe r i (2 ^ j) ∧
      ∀ e ∈ upEdges fid par pe r i (2 ^ j),
        π (fid (liftMin (fun i j => liftF par i j) pe piv r i j)) ≤ π e := by
  have hpe_lt : ∀ y < n, y ≠ r → pe y < tM := fun y hy hyr => (hR.step y hy hyr).1
  induction j with
  | zero =>
    intro i hi hne
    have hir : i ≠ r := by
      rintro rfl
      exact hne hR.par_r
    have hE : upEdges fid par pe r i (2 ^ 0) = {fid (pe i)} := by
      simp [upEdges, hir]
    rw [hE]
    refine ⟨hpe_lt i hi hir, Finset.mem_singleton_self _, fun e he => ?_⟩
    rw [Finset.mem_singleton.mp he]
    rfl
  | succ j ih =>
    intro i hi hne
    have hsplit : upEdges fid par pe r i (2 ^ (j + 1)) =
        upEdges fid par pe r i (2 ^ j) ∪ upEdges fid par pe r (liftF par i j) (2 ^ j) := by
      rw [pow_succ, mul_two, upEdges_add hR, liftF_eq_iterate]
    have hparlt : ∀ x < n, par x < n := hR.par_lt
    have hu := liftF_lt hparlt j i hi
    -- the first half moves
    have hne1 : liftF par i j ≠ i := by
      intro h
      have hir : i = r := eq_r_of_iterate_eq hR hi (Nat.one_le_two_pow)
        (by rw [← liftF_eq_iterate]; exact h)
      apply hne
      rw [liftF, h, h]
    obtain ⟨ha1, ha2, ha3⟩ := ih i hi hne1
    simp only [liftMin]
    by_cases hur : liftF par i j = r
    · rw [if_pos hur, hsplit, hur, upEdges_root, Finset.union_empty]
      exact ⟨ha1, ha2, ha3⟩
    · rw [if_neg hur]
      have hne2 : liftF par (liftF par i j) j ≠ liftF par i j := by
        intro h
        exact hur (eq_r_of_iterate_eq hR hu Nat.one_le_two_pow
          (by rw [← liftF_eq_iterate]; exact h))
      obtain ⟨hc1, hc2, hc3⟩ := ih _ hu hne2
      rw [hsplit]
      split_ifs with hlt
      · rw [hpiv _ hc1, hpiv _ ha1] at hlt
        refine ⟨hc1, Finset.mem_union_right _ hc2, fun e he => ?_⟩
        rcases Finset.mem_union.mp he with he | he
        · exact le_trans (le_of_lt hlt) (ha3 e he)
        · exact hc3 e he
      · rw [hpiv _ hc1, hpiv _ ha1] at hlt
        refine ⟨ha1, Finset.mem_union_left _ ha2, fun e he => ?_⟩
        rcases Finset.mem_union.mp he with he | he
        · exact ha3 e he
        · exact le_trans (not_lt.mp hlt) (hc3 e he)

end

end MinCostFlow.LSF.Program
