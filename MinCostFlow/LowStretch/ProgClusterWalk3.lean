module

public import MinCostFlow.LowStretch.ProgClusterWalk2

/-!
# The walk of the stem along the tree

The stem (child `0`) has as highway the highway of the cluster (no special petal) or its part
after the special portal. Both are a tail of the path of parents from the node of the target of
the cluster. `PW.walk_tail`: the path of parents from node number `j0` of a path that ends at the
node of the center gives the stored steps after `j0`, ends at the node of the center, and does not
visit it before.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

namespace PW

variable {W : PW} {w : ℕ} {mem : ℕ → ℕ} {A : TA}

/-- **A tail of the path of parents.** -/
theorem walk_tail (h : W.Ok w mem) (hT : W.Tree A mem) {v n j0 : ℕ} (hp : W.Path mem v n)
    (hj0 : j0 ≤ n) (X : PetL)
    (hX : X.PAR = W.NXT ∧ X.PP = A.PP ∧ X.PF = A.PF ∧ X.PA = A.PA ∧ X.PB = A.PB) :
    (parWalk mem X.PAR (W.pe mem v j0) (n - j0)).map (X.ent mem) =
        ((W.stp A mem v n).drop j0).map (Cl.stE W.c.half) ∧
      (∀ u ∈ parWalk mem X.PAR (W.pe mem v j0) (n - j0), u = W.sv (mem (X.PA + u))) ∧
      parEnd mem X.PAR (W.pe mem v j0) (n - j0) = W.root ∧
      W.root ∉ parWalk mem X.PAR (W.pe mem v j0) (n - j0) ∧
      (parWalk mem X.PAR (W.pe mem v j0) (n - j0)).Nodup := by
  obtain ⟨x1, x2, x3, x4, x5⟩ := hX
  have hpe : ∀ k, parEnd mem W.NXT (W.pe mem v j0) k = W.pe mem v (j0 + k) := fun k => by
    unfold pe parEnd; rw [Nat.add_comm, Function.iterate_add_apply]
  have hedge : ∀ k < n, W.pe mem v k < W.s ∧ W.pe mem v k ≠ W.root :=
    fun k hk => ⟨(hp.2 k hk).2, (hp.2 k hk).1⟩
  have hnd := hT.path_nodup hp
  have hlen := stp_length (W := W) (A := A) (mem := mem) v n
  have hpe' : parEnd mem W.NXT (W.pe mem v j0) = fun k => W.pe mem v (j0 + k) := funext hpe
  rw [parWalk_eq, x1, hpe']
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · apply List.ext_getElem (by simp [hlen])
    intro k h1 h2
    simp only [List.length_map, List.length_range] at h1
    simp only [List.getElem_map, List.getElem_range, List.getElem_drop, stp_getElem, PetL.ent,
      Cl.stE, x2, x3, x4, x5]
    have := (hT.edge _ (hedge (j0 + k) (by omega)).1 (hedge (j0 + k) (by omega)).2).2.2.2.2.2.2.2.2.2
    rw [this]
  · intro u hu
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hu
    have hk' := List.mem_range.mp hk
    rw [x4, (hT.edge _ (hedge (j0 + k) (by omega)).1 (hedge (j0 + k) (by omega)).2).2.2.1]
  · show W.pe mem v (j0 + (n - j0)) = W.root
    rw [show j0 + (n - j0) = n by omega]; exact hp.1
  · intro hmem
    obtain ⟨k, hk, hk2⟩ := List.mem_map.mp hmem
    have hk' := List.mem_range.mp hk
    exact (hedge (j0 + k) (by omega)).2 hk2
  · refine List.Nodup.map_on (fun x hx y hy hxy => ?_) List.nodup_range
    have hx' := List.mem_range.mp hx
    have hy' := List.mem_range.mp hy
    have := List.inj_on_of_nodup_map hnd (List.mem_range.mpr (show j0 + x < n + 1 by omega))
      (List.mem_range.mpr (show j0 + y < n + 1 by omega)) hxy
    omega

end PW

end MinCostFlow.LowStretch
