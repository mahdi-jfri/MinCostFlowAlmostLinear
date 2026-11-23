module

public import MinCostFlow.LinkCut.PathTree.NumCut
public import MinCostFlow.LinkCut.PathProg.Bodies
public import MinCostFlow.MinRatio.PathTreeContract

/-!
# The numbers of a fitting state have room in `treeLimbs L` limbs

The contract keeps every stored value, summary and tag of the state in `L` limbs
(`pathTreeFits`). The machine computes with `K = treeLimbs L = 4 L + 8` limbs. This file shows
that the bounds `ForestB` and `NumCtx`, which the numeric lemmas of `PathTree` take, hold with
`R = (2 n + 1) c` and `V = c + R`, where `c` is the capacity of `L` limbs
(`forestB_of_fits`, `numCtx_of_log`).

The reason is short. A tag in `L` limbs has size at most `c`, and a node has at most `2 n + 1`
tags above it, so its charge is at most `R`. An evaluated value is a stored value plus the
tags above it, so it is at most `c + R`. All of these, times `2 n + 1`, are far below the
capacity of `4 L + 8` limbs, because `2 n + 1 ≤ 2 ^ (h L + 1)`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.PathTree
  SplayState

/-- A number that fits `L` limbs is at most the capacity of `L` limbs. -/
theorem abs_le_of_fits {h L : ℕ} {z : ℤ} (hz : Fits h L z) : |z| ≤ (capacity h L : ℤ) := by
  obtain ⟨h1, h2⟩ := hz
  rw [abs_le]; constructor <;> omega

theorem valB_of_fits {h L : ℕ} {v : Option PathEdgeValue} (hv : PathEdgeFits h L v) :
    ValB (capacity h L : ℤ) v := by
  intro e he
  subst he
  obtain ⟨h1, h2, h3, h4⟩ := hv
  exact ⟨abs_le_of_fits h1, abs_le_of_fits h2, abs_le_of_fits h3, abs_le_of_fits h4⟩

theorem tagMag_le_of_fits {h L : ℕ} {t : PathTag} (hf : Fits h L t.flow)
    (hd : Fits h L t.detector) : pathTagMagnitude t ≤ (capacity h L : ℤ) := by
  unfold pathTagMagnitude
  obtain ⟨h1, h2⟩ := hf
  obtain ⟨h3, h4⟩ := hd
  have e1 : 2 * |t.flow| ≤ (capacity h L : ℤ) := by
    rcases abs_cases t.flow with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> omega
  have e2 : 2 * |t.detector| ≤ (capacity h L : ℤ) := by
    rcases abs_cases t.detector with ⟨e, -⟩ | ⟨e, -⟩ <;> rw [e] <;> omega
  omega

theorem pathTo_length_le : ∀ (t : AuxTree) (x : ℕ), (t.pathTo x).length ≤ t.countNodes
  | .leaf, _ => by simp [AuxTree.pathTo]
  | .node id l r, x => by
    have hl := pathTo_length_le l x
    have hr := pathTo_length_le r x
    simp only [AuxTree.pathTo, AuxTree.countNodes]
    split_ifs <;> simp <;> omega

theorem routeMag_le (s : SplayState (Option PathEdgeValue) PathSummary PathTag) {M : ℤ} :
    ∀ l : List ℕ, (∀ x ∈ l, pathTagMagnitude (s.nodes x).tag ≤ M) →
      pathTagRouteMagnitude s l ≤ l.length * M
  | [], _ => by simp [pathTagRouteMagnitude]
  | x :: l, hl => by
    have ih := routeMag_le s l fun y hy => hl y (List.mem_cons_of_mem _ hy)
    have hx := hl x List.mem_cons_self
    unfold pathTagRouteMagnitude at ih ⊢
    simp only [List.map_cons, List.sum_cons, List.length_cons]
    push_cast
    linarith

/-- The charge bound of a fitting state. -/
abbrev chgBound (h L n : ℕ) : ℤ := ((2 * n + 1 : ℕ) : ℤ) * (capacity h L : ℤ)

/-- The value bound of a fitting state. -/
abbrev valBound (h L n : ℕ) : ℤ := (capacity h L : ℤ) + chgBound h L n

/-- A state whose numbers fit `L` limbs has its values at most `valBound` and its charges at
most `chgBound`. -/
theorem forestB_of_fits {h L : ℕ} {st : PathTreeState} {trees : List AuxTree} {fl : List ℕ}
    {d : ℕ → ℕ} (W : LctInvWith pathPayload st trees fl d) (hf : pathTreeFits h L st) :
    ForestB st trees (valBound h L st.n) (chgBound h L st.n) := by
  have hnode : ∀ t ∈ trees, ∀ y ∈ t.toList, y ≤ 2 * st.n := fun t ht y hy => by
    have := (W.activeValid y (List.mem_flatMap.mpr ⟨t, ht, hy⟩)).2; omega
  have hroute : ∀ t ∈ trees, ∀ y ∈ t.toList, route st.splay t y ≤ chgBound h L st.n := by
    intro t ht y _
    have hle := routeMag_le st.splay (M := (capacity h L : ℤ)) (t.pathTo y) fun x hx => by
      obtain ⟨-, -, h3, h4⟩ := hf x (hnode t ht x (AuxTree.mem_pathTo hx))
      exact tagMag_le_of_fits h3 h4
    have hlen := pathTo_length_le t y
    have hsz := tree_size W ht
    have hc : (0 : ℤ) ≤ (capacity h L : ℤ) := by positivity
    have hlen' : ((t.pathTo y).length : ℤ) ≤ ((2 * st.n + 1 : ℕ) : ℤ) := by exact_mod_cast (by omega)
    unfold route chgBound
    calc _ ≤ _ := hle
      _ ≤ _ := mul_le_mul_of_nonneg_right hlen' hc
  refine ⟨fun p hp => ?_, fun t ht y hy => ?_⟩
  · obtain ⟨t, ht, hpt⟩ := List.mem_flatMap.mp hp
    have := valB_eval_of_raw st.splay t false PathTag.zero (capacity h L : ℤ) (chgBound h L st.n)
      (W.treesInv t ht).nodup (fun y hy => valB_of_fits (hf y (hnode t ht y hy)).1)
      (hroute t ht) p hpt
    simpa [pathTagMagnitude, PathTag.zero] using this
  · rw [charge_eq_route (W.treesInv t ht) hy (tree_size W ht)]
    exact hroute t ht y hy

/-- `2 n + 1` is below `2 ^ (h L + 1)` when its logarithm is at most `h L`. -/
theorem lt_two_pow_of_log {n h L : ℕ} (hlog : Nat.log 2 (2 * n + 1) ≤ h * L) :
    2 * n + 1 < 2 ^ (h * L + 1) :=
  lt_of_lt_of_le (Nat.lt_pow_succ_log_self (by norm_num) _)
    (Nat.pow_le_pow_right (by norm_num) (by omega))

/-- The room the bounds need, in natural numbers. -/
theorem room_nat {n h L : ℕ} (hh : 0 < h) (hlog : Nat.log 2 (2 * n + 1) ≤ h * L) :
    16 * ((2 * n + 1) * (2 * n + 1)) * capacity h L < capacity h (treeLimbs L) := by
  have hk := lt_two_pow_of_log hlog
  have hsq : (2 * n + 1) * (2 * n + 1) < 2 ^ (h * L + 1) * 2 ^ (h * L + 1) :=
    Nat.mul_lt_mul'' hk hk
  have hcap : capacity h (treeLimbs L) = capacity h L * 2 ^ (h * (3 * L + 8)) := by
    unfold capacity base treeLimbs
    rw [← pow_mul, ← pow_mul, ← pow_add]
    congr 1; ring
  have hp : 16 * (2 ^ (h * L + 1) * 2 ^ (h * L + 1)) ≤ 2 ^ (h * (3 * L + 8)) := by
    rw [← pow_add, show 16 = 2 ^ 4 by norm_num, ← pow_add]
    exact Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hc : 0 < capacity h L := by unfold capacity; exact pow_pos (base_pos h) _
  rw [hcap, Nat.mul_comm (capacity h L)]
  exact Nat.mul_lt_mul_of_pos_right (by omega) hc

/-- The numeric context of a fitting state. -/
theorem numCtx_of_log {n h L : ℕ} (hh : 0 < h) (hlog : Nat.log 2 (2 * n + 1) ≤ h * L) :
    NumCtx h (treeLimbs L) (2 * n + 1) (valBound h L n) (chgBound h L n) := by
  have hr := room_nat hh hlog
  have hc : (0 : ℤ) ≤ (capacity h L : ℤ) := by positivity
  refine ⟨?_, ?_, by omega, ?_⟩
  · unfold valBound chgBound; positivity
  · unfold chgBound; positivity
  · unfold Room valBound chgBound
    have hr' : (16 : ℤ) * (((2 * n + 1 : ℕ) : ℤ) * ((2 * n + 1 : ℕ) : ℤ)) * (capacity h L : ℤ) <
        (capacity h (treeLimbs L) : ℤ) := by exact_mod_cast hr
    have hk : (1 : ℤ) ≤ ((2 * n + 1 : ℕ) : ℤ) := by exact_mod_cast (by omega)
    nlinarith

end MinCostFlow.LinkCut.PathProg
