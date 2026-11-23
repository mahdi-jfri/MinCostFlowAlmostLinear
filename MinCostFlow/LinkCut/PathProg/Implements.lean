module

public import MinCostFlow.LinkCut.PathProg.OpPoint

/-!
# The path-tree program implements the Section 6 contract

`pathTree_implements`: the bodies `pathTreeBodies` at `b0` implement
`pathTreeMachineContract fmt L pathC (pathAlloc L)`, for every number of limbs `L`, with the
representation `pathRep`. The constant `pathC` is a numeral. The allocation is the arena for
the initialization and `20 (4 L + 8) + 100` words for an operation.

The initialization writes the arena of `lctInit` (`pathInitBody_runs`). Its potential is zero,
since the model's potentials of `lctInit` are zero and the stack is empty. Each operation is
handled in `OpCutLink`, `OpPath` and `OpPoint`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.PathProg

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.PathTree MinCostFlow.LinkCut.Path

theorem init_cost_aux {C L n c : ℕ} (h0 : 1000 ≤ C) (hc : c ≤ 120 * (2 * n + 1) + 200) :
    c ≤ C * (L + 1) ^ 2 * (n + 1) := by
  have h1 : 1 ≤ (L + 1) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h3 : 1000 * (n + 1) ≤ C * (n + 1) := Nat.mul_le_mul_right _ h0
  have h2 : C * (n + 1) ≤ C * (L + 1) ^ 2 * (n + 1) :=
    Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_right _ h1)
  omega

/-- The initialization pays for itself: it costs at most `120 (2 n + 1) + 200` steps and leaves
potential zero. -/
theorem init_cost (L n c : ℕ) (hc : c ≤ 120 * (2 * n + 1) + 200) :
    c + pathPhi pathC L (lctInit pathPayload n none) [] ≤ pathC * (L + 1) ^ 2 * (n + 1) := by
  have hΦ := (lctInit_spec pathPayload_laws n (none : Option PathEdgeValue)).2.1
  have hH := (lctInit_spec pathPayload_laws n (none : Option PathEdgeValue)).2.2.1
  have hz : pathPhi pathC L (lctInit pathPayload n none) [] = 0 := by
    unfold pathPhi pathTreePotential
    rw [hΦ, hH]
    rfl
  rw [hz, Nat.add_zero]
  exact init_cost_aux (by unfold pathC; norm_num) hc

theorem arenaEnd_shift (b n L : ℕ) : arenaEnd b n L = b + arenaEnd 0 n L := by
  unfold arenaEnd arenaNb; omega

/-- The path-tree program implements the Section 6 contract. -/
theorem pathTree_implements {w b0 : ℕ} {p : Program} (fmt : Format w) (L : ℕ)
    (hh : 0 < fmt.limbBits) (hw : 2 * fmt.limbBits + 2 ≤ w)
    (hp : p.HasAt b0 (pathTreeBodies fmt.limbBits b0)) :
    (pathRep fmt.limbBits L pathC).Implements w p b0 (fun i => b0 + 1 + i)
      (pathTreeMachineContract fmt L pathC (pathAlloc L)) := by
  refine ⟨pathRep_local _ _ _, ?_, ?_⟩
  · intro args mem pos ω _ hpre hz hroom
    obtain ⟨n, heap, rfl, -, -, -, -⟩ := hpre
    have hha : heapArg [n, L, heap] = heap := rfl
    have hsp : (pathTreeMachineContract fmt L pathC (pathAlloc L)).initSpace [n, L, heap] mem =
        arenaEnd 0 n L := by
      show pathAlloc L 7 n [n, L, heap] = _
      unfold pathAlloc
      rw [ite_eq_left rfl]
    rw [hha, hsp] at hroom
    rw [hha] at hz
    have hend := arenaEnd_shift heap n L
    obtain ⟨o, st', c, hr, ⟨hval, hI⟩, hc⟩ :=
      pathInitBody_runs (p := p) ω hz (by omega : arenaEnd heap n L < 2 ^ w)
    have hbody : p.procs[b0]? = some pathInitBody := core_at hp 0 (by decide)
    refine ⟨pathInitBody, hbody, o, st', c, hr, lctInit pathPayload n none,
      (lctInit pathPayload n none, []), ⟨rfl, pathInit_arena hI, pathInit_stateOk n⟩, rfl,
      ?_, init_cost L n c hc⟩
    rw [hha, hsp]
    refine ⟨by omega, by omega, hval ▸ hI.zero, fun a ha _ => hI.below a ha, fun a ha => ?_⟩
    have ha' : heap ≤ a ∧ a < arenaEnd heap n L := ha
    exact Or.inr ⟨ha'.1, by omega⟩
  · intro i b s x args mem pos ω _ hb hrep hpre hfoot hz hroom
    obtain ⟨s0, S⟩ := x
    obtain ⟨hs, hA, hok⟩ := hrep
    have hs' : s0 = s := hs
    subst hs'
    match i, hpre, hroom with
    | 0, hpre, hroom => exact link_done L hh hw hp ω hb hA hok hpre hfoot hz hroom
    | 1, hpre, hroom => exact cut_done L hh hw hp ω hb hA hok hpre hfoot hz hroom
    | 2, hpre, hroom => exact apply_done L hh hw hp ω hb hA hok hpre hfoot hz hroom
    | 3, hpre, hroom => exact summary_done L hh hw hp ω hb hA hok hpre hfoot hz hroom
    | 4, hpre, hroom => exact read_done L hh hw hp ω hb hA hok hpre hfoot hz hroom
    | 5, hpre, hroom => exact write_done L hh hw hp ω hb hA hok hpre hfoot hz hroom
    | 6, hpre, hroom => exact find_done L hh hw hp ω hb hA hok hpre hfoot hz hroom
    | _ + 7, hpre, _ => exact (hpre.2.2.2.2 : False).elim

end MinCostFlow.LinkCut.PathProg
