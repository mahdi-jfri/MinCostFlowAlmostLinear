module

public import MinCostFlow.LastLevelProgram.RootDistancePass
import MinCostFlow.Chain.WalkFlow
import Mathlib.Tactic

/-!
# Decoding the root-distance table

A tree path uses each edge once. Summing the stored edge numerators
therefore gives the exact root distance at the common length scale.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open Num LSF

/-- The numerator obtained by adding the lengths along the root path. -/
noncomputable def rootDistanceNumerator (T : MGraph) (r : ℕ) (length : ℕ → ℤ) (u : ℕ) : ℤ :=
  ∑ e ∈ walkEdges (T.forestPath u r), length e

/-- A root-path numerator decodes to the path length at the input scale. -/
theorem rootDistanceNumerator_decode {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (length : ℕ → ℤ) (P : ℕ) :
    (rootDistanceNumerator T r length u : ℝ) / (2 : ℝ)^P =
      walkLength (fun e => (length e : ℝ) / (2 : ℝ)^P) (T.forestPath u r) := by
  rw [walkLength_eq_sum_of_isPath _ (forestPath_isPath hT.isForest (hT.connected_root hu))]
  simp only [rootDistanceNumerator, Int.cast_sum, Finset.sum_div]

/-- The root is initialized with the empty-path numerator. -/
theorem rootDistanceNumerator_root {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (length : ℕ → ℤ) :
    rootDistanceNumerator T r length r = 0 := by
  simp [rootDistanceNumerator, forestPath_self hT.isForest, walkEdges]

/-- Each visit adds one stored edge length to the parent's numerator. -/
theorem rootDistanceNumerator_step {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (hne : u ≠ r) (length : ℕ → ℤ) :
    rootDistanceNumerator T r length u =
      rootDistanceNumerator T r length (parent T r u) + length (parentEdge T r u) := by
  have hv := parent_mem hT hu
  have he := rootDistance_parent_step hT hu hne (fun e => (length e : ℝ))
  have ha := rootDistanceNumerator_decode hT hu length 0
  have hb := rootDistanceNumerator_decode hT hv length 0
  simp only [pow_zero, div_one] at ha hb
  rw [← ha, ← hb] at he
  exact_mod_cast (he.trans (add_comm _ _))

/-- A block containing the accumulated numerator stores the exact root distance. -/
theorem rootDistanceBlock_decode {T : MGraph} {r u : ℕ} (hT : IsRootedTree T r)
    (hu : u ∈ T.V) (mem : ℕ → ℕ) (length : ℕ → ℤ) (a h L P : ℕ)
    (hval : intVal mem a h L = rootDistanceNumerator T r length u) :
    fixVal mem a h L P =
      walkLength (fun e => (length e : ℝ) / (2 : ℝ)^P) (T.forestPath u r) := by
  rw [fixVal,hval,rootDistanceNumerator_decode hT hu]

/-- The machine pass's arithmetic premise follows from the parent and
parent-edge tables and the limb bounds on the root-path numerators. -/
theorem rootDistancePass_inputs {T : MGraph} {r : ℕ} (hT : IsRootedTree T r)
    (mem : ℕ → ℕ) (length : ℕ → ℤ) (h L lengths k : ℕ)
    (child par edge : ℕ → ℕ)
    (hchild : ∀ i < k, child i ∈ T.V ∧ child i ≠ r)
    (hpar : ∀ i < k, par i = parent T r (child i))
    (hedge : ∀ i < k, edge i = parentEdge T r (child i))
    (hblocks : ∀ e ∈ T.E, Valid mem (lengths+e*L) h L ∧ intVal mem (lengths+e*L) h L = length e)
    (hfit : ∀ u ∈ T.V, Fits h L (rootDistanceNumerator T r length u)) :
    ∀ i < k, Valid mem (lengths+edge i*L) h L ∧
      Fits h L (rootDistanceNumerator T r length (child i)) ∧
      rootDistanceNumerator T r length (child i) =
        rootDistanceNumerator T r length (par i) + intVal mem (lengths+edge i*L) h L := by
  intro i hi
  obtain ⟨hu,hne⟩ := hchild i hi
  have he : edge i ∈ T.E := by rw [hedge i hi]; exact parentEdge_mem hT hu hne
  obtain ⟨hv,hn⟩ := hblocks _ he
  refine ⟨hv,hfit _ hu,?_⟩
  rw [hn,hpar i hi,hedge i hi,rootDistanceNumerator_step hT hu hne]

/-- Each tree edge contributes at most `B`, so the numerator grows
by at most `B` for every level below the root. -/
theorem rootDistanceNumerator_bound {T : MGraph} {r u : ℕ}
    (hT : IsRootedTree T r) (hu : u ∈ T.V) (length : ℕ → ℤ) (B : ℕ)
    (hbound : ∀ e ∈ T.E, 0 ≤ length e ∧ length e ≤ (B : ℤ)) :
    0 ≤ rootDistanceNumerator T r length u ∧
      rootDistanceNumerator T r length u ≤ (depth T r u : ℤ) * B := by
  have aux (d : ℕ) : ∀ x ∈ T.V, depth T r x = d →
      0 ≤ rootDistanceNumerator T r length x ∧
        rootDistanceNumerator T r length x ≤ (d : ℤ) * B := by
    induction d with
    | zero =>
      intro x hx hd
      have he : r = x := (isAncestor_eq_iff_depth hT hx (isAncestor_root hT hx)).1
        ((rootDistance_at_root hT (fun _ => 0)).1.trans hd.symm)
      subst x
      simp [rootDistanceNumerator_root hT]
    | succ d ih =>
      intro x hx hd
      have hne : x ≠ r := by
        intro he
        subst x
        exact Nat.noConfusion (((rootDistance_at_root hT (fun _ => 0)).1).symm.trans hd)
      have hp : depth T r (parent T r x) = d :=
        Nat.succ.inj ((depth_parent hT hx hne).trans hd)
      obtain ⟨hp0,hpB⟩ := ih _ (parent_mem hT hx) hp
      obtain ⟨he0,heB⟩ := hbound _ (parentEdge_mem hT hx hne)
      rw [rootDistanceNumerator_step hT hx hne]
      refine ⟨add_nonneg hp0 he0,?_⟩
      simpa only [Nat.cast_succ,add_mul,one_mul] using add_le_add hpB heB
  exact aux _ u hu rfl

/-- One common limb width suffices for every root-distance block
when its signed capacity exceeds twice the vertex-count length bound. -/
theorem rootDistanceNumerator_fits {T : MGraph} {r u : ℕ}
    (hT : IsRootedTree T r) (hu : u ∈ T.V) (length : ℕ → ℤ) (B h L : ℕ)
    (hbound : ∀ e ∈ T.E, 0 ≤ length e ∧ length e ≤ (B : ℤ))
    (hcap : 2*T.V.card*B < capacity h L) :
    Fits h L (rootDistanceNumerator T r length u) := by
  obtain ⟨hlo,hhi⟩ := rootDistanceNumerator_bound hT hu length B hbound
  have hd : (depth T r u : ℤ) ≤ (T.V.card : ℤ) := by
    exact_mod_cast (depth_lt_card_vertices hT hu).le
  have hsize := hhi.trans (mul_le_mul_of_nonneg_right hd (Int.natCast_nonneg B))
  have hcap' : 2*(T.V.card : ℤ)*(B : ℤ) < (capacity h L : ℤ) := by exact_mod_cast hcap
  unfold Fits
  constructor
  · have hn : 0 ≤ (capacity h L : ℤ) := Int.natCast_nonneg _
    omega
  · calc
      2 * rootDistanceNumerator T r length u ≤ 2 * ((T.V.card : ℤ) * B) :=
        mul_le_mul_of_nonneg_left hsize (by decide)
      _ < (capacity h L : ℤ) := by simpa only [mul_assoc] using hcap'

end MinCostFlow.LastLevelProgram
