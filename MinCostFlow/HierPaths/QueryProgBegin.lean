module

public import MinCostFlow.HierPaths.QueryProgMain

/-!
# Scratch addresses for GetPath

The first seven assignments compute the capacity and buffer addresses from the hierarchy
header. The mutable state below the heap and the scratch cells are preserved.
-/

public section

namespace MinCostFlow.HierPaths

open WordRAM

/-- The query starts by reserving four buffers of the calculated capacity. -/
theorem queryBegin_triple {w : ℕ} {p : Program} {X : HierConcrete} {mem : ℕ → ℕ}
    {b u v out pos : ℕ} (h : ListAt mem b X.encode) (hblock : b + X.encode.length ≤ out)
    (hdepthW : 2 ^ X.depth + 1 < 2 ^ w) (hw : out + 6 * X.queryCapacity + 3 < 2 ^ w) :
    let cap := X.queryCapacity
    let first := out + (2 * cap + 3)
    Triple w p (fun st => st = startState [b, u, v, out] mem pos) queryBegin
      (normalPost fun st =>
        st.mem = mem ∧ st.regs 0 = b ∧ st.regs 1 = u ∧ st.regs 2 = v ∧ st.regs 3 = out ∧
        st.regs 4 = X.depth ∧ st.regs 5 = X.H.lam ∧ st.regs 6 = cap ∧
        st.regs 7 = first ∧ st.regs 8 = first + cap ∧ st.regs 9 = first + cap + cap ∧
        st.regs 10 = first + cap + cap + cap) (fun _ => 100) := by
  dsimp only
  intro st ω hst
  subst st
  obtain ⟨hL0, hE0⟩ := block_sec h (i := 0) (by decide)
  change ListAt mem _ X.header at hL0
  change _ + X.header.length ≤ _ at hE0
  have hlen : X.header.length = 15 := rfl
  have hD : mem (b + 25 + mem (b + 0) + 7) = X.depth := hL0 7 (by omega)
  have hL : mem (b + 25 + mem (b + 0) + 10) = X.H.lam := hL0 10 (by omega)
  suffices hrun : ∃ o st' c, Runs w p ω queryBegin (startState [b, u, v, out] mem pos) o st' c ∧
      normalPost (fun st =>
        st.mem = mem ∧ st.regs 0 = b ∧ st.regs 1 = u ∧ st.regs 2 = v ∧ st.regs 3 = out ∧
        st.regs 4 = X.depth ∧ st.regs 5 = X.H.lam ∧ st.regs 6 = X.queryCapacity ∧
        st.regs 7 = out + (2 * X.queryCapacity + 3) ∧
        st.regs 8 = out + (2 * X.queryCapacity + 3) + X.queryCapacity ∧
        st.regs 9 = out + (2 * X.queryCapacity + 3) + X.queryCapacity + X.queryCapacity ∧
        st.regs 10 = out + (2 * X.queryCapacity + 3) + X.queryCapacity + X.queryCapacity +
          X.queryCapacity) o st' ∧ 0 + c ≤ 100 by
    simpa only [Nat.zero_add] using hrun
  unfold queryBegin queryHeaderExpr secExpr startState
  wram_step
  simp only [hD]
  wram_step
  simp only [hL]
  have h1 : 1 < 2 ^ w := by omega
  have hshift : 1 <<< X.depth = 2 ^ X.depth := by simp [Nat.shiftLeft_eq]
  have hshiftW : 1 <<< X.depth < 2 ^ w := by rw [hshift]; omega
  have hmul : (1 <<< X.depth) + 1 = 2 ^ X.depth + 1 := by rw [hshift]
  have hcapEq : ((1 <<< X.depth) + 1) * X.H.lam = X.queryCapacity := by
    rw [hmul, HierConcrete.queryCapacity]
  have hcapW : ((1 <<< X.depth) + 1) * X.H.lam < 2 ^ w := by rw [hcapEq]; omega
  refine runs_seq_assign_le
    (Expr.eval_mul
      (Expr.eval_add (Expr.eval_shiftLeft (Expr.eval_const h1)
        (a := .const 1) (b := .reg 4) (by eval_expr) hshiftW)
        (Expr.eval_const h1) (by rwa [hmul]))
      (b := .reg 5) (by eval_expr) hcapW) ?_
  simp only [hcapEq]
  wram_step
  wram_step
  wram_step
  refine runs_assign_le (by eval_expr) ?_ ?_
  · simp [startState, hD, hL]
  · wram_cost

end MinCostFlow.HierPaths
