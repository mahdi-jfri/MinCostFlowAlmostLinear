module

public import MinCostFlow.LinkCut.Gen.Splay
public import MinCostFlow.LinkCut.SplayOps

/-!
# The cost of a splay against the model's count

The model counts a splay of a node at depth `d` as `d / 2` half rotations. The program
`splayBody` costs one push per node on the path and one splay step per two levels
(`splayCost`). In a valid tree these are at most a constant times `d / 2 + 1`
(`splayCost_le`). The constant is `splayRate S`, which is a small multiple of the cost of one
payload step.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen SplayState

variable {α σ τ : Type*}

/-- The loop makes at most `d / 2 + d % 2` steps on a node at depth `d` with a clean path. -/
theorem splayLoopSteps_le {P : LctPayload α σ τ} (hL : P.Laws) :
    ∀ {fuel : ℕ} {st : SplayState α σ τ} {t : AuxTree} {x : ℕ},
      TreeInv P st t → x ∈ t.toList →
      t.depthOf x / 2 + t.depthOf x % 2 ≤ fuel →
      (∀ u ∈ t.pathTo x, (st.nodes u).rev = false ∧ (st.nodes u).tag = P.idTag) →
      splayLoopSteps P st fuel x ≤ t.depthOf x / 2 + t.depthOf x % 2 := by
  intro fuel
  induction fuel with
  | zero => intro st t x _ _ _ _; simp [splayLoopSteps]
  | succ k ih =>
    intro st t x ht hx hfuel hclean
    have hx_nz : x ≠ 0 := SubtreeInv_nonZero ht.sub hx
    have hpar_eq : (st.nodes x).par = t.parentIn x 0 :=
      SubtreeInv_par_eq_parentIn ht.nodup ht.sub hx
    by_cases hxr : x = t.rootId
    · have hpar0 : (st.nodes x).par = 0 := by
        rw [hpar_eq, hxr]; exact parentIn_rootId 0
      simp [splayLoopSteps, hx_nz, hpar0]
    · have hpm := AuxTree.parentIn_mem_and_depth (p₀ := 0) ht.nodup hx hxr
      have hp_nz : (st.nodes x).par ≠ 0 := hpar_eq ▸ SubtreeInv_nonZero ht.sub hpm.1
      have hsteps : splayLoopSteps P st (k + 1) x =
          1 + splayLoopSteps P (splayStep P st x) k x := by
        simp [splayLoopSteps, hx_nz, hp_nz]
      rw [hsteps]
      rcases splayStep_preserves hL ht hx hxr hclean with
        ⟨t₁, ht₁, hperm₁, -, -, -, hrt₁, hpath₁, hzig₁, hdbl₁⟩
      have hx₁ : x ∈ t₁.toList := hperm₁.mem_iff.mpr hx
      have hclean₁ : ∀ u ∈ t₁.pathTo x, ((splayStep P st x).nodes u).rev = false ∧
          ((splayStep P st x).nodes u).tag = P.idTag := by
        intro u hu
        have hu' : u ∈ t.pathTo x := hpath₁ u hu
        rw [(hrt₁ u (AuxTree.mem_pathTo hu')).1, (hrt₁ u (AuxTree.mem_pathTo hu')).2]
        exact hclean u hu'
      have hdep_nz : t.depthOf x ≠ 0 := fun h0 => hxr ((AuxTree.depthOf_zero_iff_root hx).mp h0)
      by_cases hdep1 : t.depthOf x = 1
      · rcases hzig₁ hdep1 with ⟨hr₁, hd₁, -⟩
        have := ih ht₁ hx₁ (by rw [hd₁]; omega) hclean₁
        rw [hd₁] at this
        omega
      · rcases hdbl₁ (by omega) with ⟨hd₁, -⟩
        have := ih ht₁ hx₁ (by rw [hd₁]; omega) hclean₁
        rw [hd₁] at this
        omega

/-- The cost of one level of a splay: a push, and half a splay step, with slack. -/
def splayRate {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) : ℕ :=
  2 * (pushDownCost S + 80) + 2 * (splayStepCost S + 60) + 40

private theorem arith {d a b : ℕ} (hs : d / 2 + d % 2 + 1 ≤ d / 2 + 2) :
    (d + 1) * a + (d / 2 + d % 2 + 1) * b + 40 ≤ (d / 2 + 1) * (2 * a + 2 * b + 40) := by
  have h1 : d + 1 ≤ 2 * (d / 2 + 1) := by omega
  have h2 : d / 2 + d % 2 + 1 ≤ 2 * (d / 2 + 1) := by omega
  have e1 := Nat.mul_le_mul_right a h1
  have e2 := Nat.mul_le_mul_right b h2
  have e3 : 40 ≤ (d / 2 + 1) * 40 := Nat.le_mul_of_pos_left 40 (by omega)
  nlinarith

/-- A splay of a node of a valid tree costs at most `splayRate S` per half rotation, plus one. -/
theorem splayCost_le {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (hL : P.Laws) (S : PayloadSteps w p P Lay ok)
    {st : SplayState α σ τ} {t : AuxTree} {x fuel : ℕ}
    (ht : TreeInv P st t) (hx : x ∈ t.toList) (hf : t.depthOf x < fuel) :
    splayCost S st fuel x ≤ (splayDepth st fuel x / 2 + 1) * splayRate S := by
  rw [splayDepth_eq_depthOf ht hx hf]
  rcases pushPath_preserves hL ht hx hf with ⟨t₁, ht₁, hperm₁, -, hdep₁, -, -, hclean₁, -⟩
  have hx₁ : x ∈ t₁.toList := hperm₁.mem_iff.mpr hx
  have hsteps := splayLoopSteps_le (fuel := fuel) hL ht₁ hx₁ (by rw [hdep₁ x]; omega) hclean₁
  rw [hdep₁ x] at hsteps
  unfold splayCost splayRate
  rw [splayDepth_eq_depthOf ht hx hf]
  clear hdep₁
  set d := t.depthOf x
  calc (d + 1) * (pushDownCost S + 80) +
        (splayLoopSteps P (pushPath P st fuel x) fuel x + 1) * (splayStepCost S + 60) + 40
      ≤ (d + 1) * (pushDownCost S + 80) + (d / 2 + d % 2 + 1) * (splayStepCost S + 60) + 40 := by
        have := Nat.mul_le_mul_right (splayStepCost S + 60) (Nat.add_le_add_right hsteps 1)
        omega
    _ ≤ _ := arith (by omega)

end MinCostFlow.LinkCut.PathProg
