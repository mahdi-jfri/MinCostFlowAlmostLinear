module

public import MinCostFlow.HierPaths.BuildProgEraseProc
public import MinCostFlow.HierPaths.BuildProgVerts

/-!
# From a routed walk to its shortcut

The router returns each path as a walk of edges, and the builder stores its shortcut
`erase E u wk`. `pathProc`, called with `[ws, len, u, ends, vs, P, out]`, lists the vertices
of the walk at `vs` (`vertsProc`) and then writes the shortcut at `out` (`buildEraseProc`)
(`pathProc_meetsContract`). The array `P` must be `0` at the vertices of the walk, and the
scratch space `vs, …, vs + len` and the array lie below `out`. The cost is linear in the
length of the walk.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- `r7 := verts(ws, len, u, ends, vs); r8 := erase(ws, len, vs, P, out); return r8`. -/
def pathProc (fVerts fErase : ℕ) : Stmt :=
  .seq (.call 7 fVerts [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4])
    (.seq (.call 8 fErase [.reg 0, .reg 1, .reg 4, .reg 5, .reg 6]) (.ret (.reg 8)))

/-- What memory holds before `pathProc`. -/
structure PathPre (w : ℕ) (E : List (ℕ × ℕ)) (u : ℕ) (wk : List ℕ) (mem : ℕ → ℕ)
    (ws len ends vs P out : ℕ) : Prop where
  verts : VertsPre w E u wk mem ws len ends vs
  zero : ∀ v ∈ walkVerts E u wk, mem (P + v) = 0
  vs_lt : vs + len + 1 ≤ out
  P_ge : ∀ v ∈ walkVerts E u wk, vs + len + 1 ≤ P + v
  P_lt : ∀ v ∈ walkVerts E u wk, P + v < out
  out_lt : out + len < 2 ^ w
  u_lt : u < 2 ^ w
  ends_lt : ends < 2 ^ w

/-- The contract of `pathProc`. -/
def pathContract (w : ℕ) (E : List (ℕ × ℕ)) (u : ℕ) (wk : List ℕ) : Contract where
  pre args mem := ∃ ws len ends vs P out, args = [ws, len, u, ends, vs, P, out] ∧
    PathPre w E u wk mem ws len ends vs P out
  post args mem v mem' := ∃ ws len ends vs P out, args = [ws, len, u, ends, vs, P, out] ∧
    v = (erase E u wk).length ∧ (∀ t < v, mem' (out + t) = (erase E u wk).getD t 0) ∧
    ∀ x, (x < vs ∨ (vs + len + 1 ≤ x ∧ x < out) ∨ out + len ≤ x) → mem' x = mem x
  cost args _ := 136 * args.getD 1 0 + 220

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

variable {w : ℕ} {E : List (ℕ × ℕ)} {u : ℕ} {wk : List ℕ}

/-- **`pathProc` writes the shortcut of a routed walk.** -/
theorem pathProc_meetsContract {p : Program} {f fVerts fErase fFill fJump fClear : ℕ}
    (hp : p.procs[f]? = some (pathProc fVerts fErase))
    (hV : p.procs[fVerts]? = some vertsProc)
    (hE : p.procs[fErase]? = some (buildEraseProc fFill fJump fClear))
    (hF : p.procs[fFill]? = some posFillProc) (hJ : p.procs[fJump]? = some jumpProc)
    (hC : p.procs[fClear]? = some posClearProc) :
    MeetsContract w p f (pathContract w E u wk) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨ws, len, ends, vs, P, out, rfl, hpre⟩
  have hvp := hpre.verts
  have hlen := hvp.len_eq
  have hwl := hvp.ws_lt
  have hvl := hpre.vs_lt
  have hout := hpre.out_lt
  have hu := hpre.u_lt
  have he := hpre.ends_lt
  have hw := hvp.hw
  refine runs_start_le ?_
  dsimp only [pathProc]
  refine runs_seq_call_le (vertsProc_meetsContract (w := w) (E := E) (u := u) (wk := wk) hV)
    (vs := [ws, len, u, ends, vs]) (by simp [evalArgs, Expr.eval, startState]) ?_
    ⟨ws, len, ends, vs, rfl, hvp⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  intro v₁ mem₁ pos₁ hpost₁
  obtain ⟨_, _, _, _, hargs₁, hv₁, hf₁⟩ := hpost₁
  simp only [List.cons.injEq, and_true] at hargs₁
  obtain ⟨rfl, rfl, -, rfl, rfl⟩ := hargs₁
  simp only [startState] at hv₁ hf₁
  have hepre : ErasePre w E u wk mem₁ ws len vs P out :=
    ⟨hlen, fun k hk => by rw [hf₁ _ (Or.inl (by omega))]; exact hvp.edges k hk, hv₁,
      fun v hv => by rw [hf₁ _ (Or.inr (hpre.P_ge v hv))]; exact hpre.zero v hv,
      by omega, hvl,
      fun v hv => ⟨by have := hpre.P_ge v hv; omega, hpre.P_ge v hv⟩, hpre.P_lt, hout, hw⟩
  refine runs_seq_call_le (buildEraseProc_meetsContract (w := w) (E := E) (u := u) (wk := wk)
    hE hF hJ hC) (vs := [ws, len, vs, P, out])
    (by simp [evalArgs, Expr.eval, Function.update, startState]) ?_
    ⟨ws, len, vs, P, out, rfl, hepre⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hv0 : u ∈ walkVerts E u wk := by cases wk <;> simp [walkVerts]
    have := hpre.P_lt u hv0
    rcases ha with rfl | rfl | rfl | rfl | rfl <;> omega
  intro v₂ mem₂ pos₂ hpost₂
  obtain ⟨_, _, _, _, _, hargs₂, hv₂, hout₂, hf₂⟩ := hpost₂
  simp only [List.cons.injEq, and_true] at hargs₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs₂
  dsimp only at hf₂ hout₂
  refine runs_ret_le (v := v₂) (by simp [Expr.eval, Function.update])
    ⟨ws, len, ends, vs, P, out, rfl, hv₂, hout₂, fun x hx => ?_⟩ ?_
  · dsimp only
    rw [hf₂ x (by omega), hf₁ x (by omega)]
  · simp only [pathContract, vertsContract, buildEraseContract, List.getD_cons_succ,
      List.getD_cons_zero, argsSize, Expr.size_reg]
    omega

end MinCostFlow.HierPaths
