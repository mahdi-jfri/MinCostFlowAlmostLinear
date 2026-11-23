module

public import MinCostFlow.HierPaths.InitProgFlatEnd

/-!
# A substitution loop step

The two calls in a loop step append the directed embedding and advance the
current terminal. The output pointer and terminal are kept in separate registers.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- Registers 0, 1 and 2 hold the graph address, embedding address and edge count.
Registers 6, 7 and 9 hold the output pointer, current terminal and input edge. -/
def initFlatStep (edge finish : ℕ) : Stmt :=
  .call 6 edge [.reg 0, .reg 1, .reg 2, .reg 9, .reg 7, .reg 6] ;;
  .call 7 finish [.reg 0, .reg 9, .reg 7]

theorem initFlatStep_noRand (edge finish : ℕ) : (initFlatStep edge finish).NoRand := by
  simp [initFlatStep, Stmt.NoRand]

theorem initFlatStep_triple {w edge finish : ℕ} {p : Program} {G : Graph}
    {emb : ℕ → List ℕ} {g a e u dst : ℕ} {s : State}
    (hEdge : MeetsContract w p edge (initFlatEdgeContract w G emb e u))
    (hEnd : MeetsContract w p finish (initFlatEndContract w G e u))
    (hwords : ∀ x ∈ [g, a, G.m, e, u, dst], x < 2 ^ w)
    (hEdgePre : (initFlatEdgeContract w G emb e u).pre [g, a, G.m, e, u, dst] s.mem)
    (hEndPre : ∀ mem, (∀ y < dst, mem y = s.mem y) →
      (initFlatEndContract w G e u).pre [g, e, u] mem)
    (r0 : s.regs 0 = g) (r1 : s.regs 1 = a) (r2 : s.regs 2 = G.m)
    (r6 : s.regs 6 = dst) (r7 : s.regs 7 = u) (r9 : s.regs 9 = e) :
    Triple w p (fun t => t = s) (initFlatStep edge finish)
      (normalPost fun t => t.regs =
        Function.update (Function.update s.regs 6 (dst + (emb e).length)) 7
          (otherEnd G.edges e u) ∧
        ListAt t.mem dst (initFlatEdgeWords G emb e u) ∧
        ∀ y, y < dst ∨ dst + (emb e).length ≤ y → t.mem y = s.mem y)
      (fun _ => 30 * (emb e).length + 180) := by
  intro st ω hs
  subst st
  refine runs_start_le ?_
  unfold initFlatStep
  refine runs_seq_call_le hEdge
    (vs := [g, a, G.m, e, u, dst]) (by simp [evalArgs, Expr.eval, r0, r1, r2, r6, r7, r9])
    hwords hEdgePre ?_
  intro v mem₁ pos₁ hp
  obtain ⟨g', a', dst', hargs, hv, hw, hf⟩ := hp
  simp only [List.cons.injEq, and_true] at hargs
  obtain ⟨_, _, _, _, _, hd⟩ := hargs
  subst dst' v
  refine runs_call_le hEnd (vs := [g, e, u])
    (by simp [evalArgs, Expr.eval, r0, r7, r9]) ?_ (hEndPre mem₁ fun y hy => hf y (.inl hy)) ?_
  · intro y hy
    exact hwords y (by simp at hy ⊢; tauto)
  · intro r mem₂ pos₂ hp₂
    obtain ⟨hr, hm⟩ := hp₂
    subst r mem₂
    refine ⟨⟨rfl, hw, hf⟩, ?_⟩
    simp [initFlatEdgeContract, initFlatEndContract, argsSize, Expr.size]
    omega

end MinCostFlow.HierPaths

end
