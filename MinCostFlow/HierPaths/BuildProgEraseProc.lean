module

public import MinCostFlow.HierPaths.BuildProgJump

/-!
# The linear shortcut as one procedure

`buildEraseProc fFill fJump fClear`, called with `[ws, len, vs, P, out]`, runs the three passes of
the linear shortcut: `posFillProc` writes the positions into the array at `P`, `jumpProc` writes
`erase E u w` at `out`, and `posClearProc` writes `0` back into the array. The array must be `0`
at the vertices of the walk before the call, and it is the same after the call
(`buildEraseProc_meetsContract`). The cost is linear in the length of the walk.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- `r5 := fill(vs, len + 1, P); r6 := jump(ws, len, vs, P, out); r7 := clear(vs, len + 1, P);
return r6`. -/
def buildEraseProc (fFill fJump fClear : ℕ) : Stmt :=
  .seq (.call 5 fFill [.reg 2, .bin .add (.reg 1) (.const 1), .reg 3])
    (.seq (.call 6 fJump [.reg 0, .reg 1, .reg 2, .reg 3, .reg 4])
      (.seq (.call 7 fClear [.reg 2, .bin .add (.reg 1) (.const 1), .reg 3]) (.ret (.reg 6))))

/-- What memory holds before the shortcut of the walk `wk` from `u`. -/
structure ErasePre (w : ℕ) (E : List (ℕ × ℕ)) (u : ℕ) (wk : List ℕ) (mem : ℕ → ℕ)
    (ws len vs P out : ℕ) : Prop where
  len_eq : len = wk.length
  edges : ∀ k < len, mem (ws + k) = wk.getD k 0
  verts : ∀ t ≤ len, mem (vs + t) = (walkVerts E u wk).getD t 0
  zero : ∀ v ∈ walkVerts E u wk, mem (P + v) = 0
  ws_lt : ws + len ≤ out
  vs_lt : vs + len + 1 ≤ out
  P_ge : ∀ v ∈ walkVerts E u wk, ws + len ≤ P + v ∧ vs + len + 1 ≤ P + v
  P_lt : ∀ v ∈ walkVerts E u wk, P + v < out
  out_lt : out + len < 2 ^ w
  hw : 1 < 2 ^ w

/-- The contract of `buildEraseProc`. -/
def buildEraseContract (w : ℕ) (E : List (ℕ × ℕ)) (u : ℕ) (wk : List ℕ) : Contract where
  pre args mem := ∃ ws len vs P out, args = [ws, len, vs, P, out] ∧
    ErasePre w E u wk mem ws len vs P out
  post args mem v mem' := ∃ ws len vs P out, args = [ws, len, vs, P, out] ∧
    v = (erase E u wk).length ∧ (∀ t < v, mem' (out + t) = (erase E u wk).getD t 0) ∧
    ∀ x, (x < out ∨ out + len ≤ x) → mem' x = mem x
  cost args _ := 80 * args.getD 1 0 + 150

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- Pass 1 changes only the cells `P + vs_j`. -/
theorem fillMem_off {mem₀ : ℕ → ℕ} {vs n P x : ℕ} :
    ∀ i, (∀ j < i, x ≠ P + mem₀ (vs + j)) → fillMem mem₀ vs n P i x = mem₀ x
  | 0, _ => rfl
  | i + 1, h => by
    simp only [fillMem]
    rw [Function.update_of_ne (h i (by omega))]
    exact fillMem_off i fun j hj => h j (by omega)

variable {w : ℕ} {E : List (ℕ × ℕ)} {u : ℕ} {wk : List ℕ}

/-- **The linear shortcut meets its contract.** -/
theorem buildEraseProc_meetsContract {p : Program} {f fFill fJump fClear : ℕ}
    (hp : p.procs[f]? = some (buildEraseProc fFill fJump fClear))
    (hF : p.procs[fFill]? = some posFillProc) (hJ : p.procs[fJump]? = some jumpProc)
    (hC : p.procs[fClear]? = some posClearProc) :
    MeetsContract w p f (buildEraseContract w E u wk) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨ws, len, vs, P, out, rfl, hpre⟩
  have hlen := hpre.len_eq
  have hw := hpre.hw
  have hout := hpre.out_lt
  have hvsl := hpre.vs_lt
  have hwsl := hpre.ws_lt
  set Vs := walkVerts E u wk
  have hVl : Vs.length = len + 1 := by rw [length_walkVerts]; omega
  have hVmem : ∀ j < len + 1, mem (vs + j) ∈ Vs := fun j hj => by
    rw [hpre.verts j (by omega)]; exact getD_mem_walkVerts (by omega)
  refine runs_start_le ?_
  dsimp only [buildEraseProc]
  have hl1 : len + 1 < 2 ^ w := by omega
  -- pass 1
  refine runs_seq_call_le (posFillProc_meetsContract (w := w) hF) (vs := [vs, len + 1, P])
    (by simp [evalArgs, Expr.eval, BinOp.eval, startState, hl1, hw]) ?_ ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hv0 := hVmem 0 (by omega)
    rcases ha with rfl | rfl | rfl
    · omega
    · omega
    · have := hpre.P_lt _ hv0; omega
  · refine ⟨vs, len + 1, P, rfl, by omega, hw, fun j hj => ?_⟩
    have hv := hVmem j hj
    exact ⟨by have := (hpre.P_ge _ hv).2; simp [startState]; omega,
      by have := hpre.P_lt _ hv; simp [startState]; omega⟩
  intro v₁ mem₁ pos₁ hpost₁
  obtain ⟨_, _, _, hargs₁, hmem₁⟩ := hpost₁
  simp only [List.cons.injEq, and_true] at hargs₁
  obtain ⟨rfl, rfl, rfl⟩ := hargs₁
  simp only [startState] at hmem₁
  have hcells : ∀ x, (∀ v ∈ Vs, x ≠ P + v) → mem₁ x = mem x := fun x hx => by
    rw [hmem₁]
    exact fillMem_off _ fun j hj => hx _ (hVmem j hj)
  have hL : ∀ j < Vs.length, mem (vs + j) = Vs.getD j 0 := fun j hj =>
    hpre.verts j (by omega)
  have hpos₁ : ∀ v ∈ Vs, mem₁ (P + v) = posFill E u wk (fun y => mem (P + y)) v := by
    intro v _
    rw [hmem₁, ← hVl]
    exact fillMem_eq_posFill E u wk hL v
  -- pass 2
  have hjpre : JumpPre w E u wk (fun y => mem (P + y)) mem₁ ws len vs P out :=
    ⟨hlen, fun k hk => by
        rw [hcells _ fun v hv => by have := (hpre.P_ge v hv).1; omega]; exact hpre.edges k hk,
      fun t ht => by
        rw [hcells _ fun v hv => by have := (hpre.P_ge v hv).2; omega]; exact hpre.verts t ht,
      hpos₁, hpre.ws_lt, hpre.vs_lt, hpre.P_lt, hout, hw⟩
  refine runs_seq_call_le (jumpProc_meetsContract (w := w) (E := E) (u := u) (wk := wk)
    (Q := fun y => mem (P + y)) hJ) (vs := [ws, len, vs, P, out])
    (by simp [evalArgs, Expr.eval, Function.update, startState]) ?_ ⟨ws, len, vs, P, out, rfl, hjpre⟩ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hv0 := hVmem 0 (by omega)
    rcases ha with rfl | rfl | rfl | rfl | rfl <;>
      first | omega | (have := hpre.P_lt _ hv0; omega)
  intro v₂ mem₂ pos₂ hpost₂
  obtain ⟨_, _, _, _, _, hargs₂, hv₂, hout₂, hframe₂⟩ := hpost₂
  simp only [List.cons.injEq, and_true] at hargs₂
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := hargs₂
  dsimp only at hframe₂ hout₂
  -- pass 3
  have hvs₂ : ∀ j < len + 1, mem₂ (vs + j) = mem (vs + j) := fun j hj => by
    rw [hframe₂ _ (Or.inl (by have := hpre.vs_lt; omega)),
      hcells _ fun v hv => by have := (hpre.P_ge v hv).2; omega]
  refine runs_seq_call_le (posClearProc_meetsContract (w := w) hC) (vs := [vs, len + 1, P])
    (by simp [evalArgs, Expr.eval, BinOp.eval, Function.update, startState, hl1, hw]) ?_ ?_ ?_
  · intro a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    have hv0 := hVmem 0 (by omega)
    rcases ha with rfl | rfl | rfl
    · omega
    · omega
    · have := hpre.P_lt _ hv0; omega
  · refine ⟨vs, len + 1, P, rfl, by omega, hw, fun j hj => ?_⟩
    have hv := hVmem j hj
    dsimp only
    rw [hvs₂ j hj]
    exact ⟨by have := (hpre.P_ge _ hv).2; omega, by have := hpre.P_lt _ hv; omega⟩
  intro v₃ mem₃ pos₃ hpost₃
  obtain ⟨_, _, _, hargs₃, hz₃, hf₃⟩ := hpost₃
  simp only [List.cons.injEq, and_true] at hargs₃
  obtain ⟨rfl, rfl, rfl⟩ := hargs₃
  dsimp only at hz₃ hf₃
  have hf₃' : ∀ x, (∀ v ∈ Vs, x ≠ P + v) → mem₃ x = mem₂ x := fun x hx =>
    hf₃ x fun j hj => by rw [hvs₂ j hj]; exact hx _ (hVmem j hj)
  refine runs_ret_le (v := v₂) (by simp [Expr.eval, Function.update]) ⟨ws, len, vs, P, out, rfl,
    hv₂, ?_, ?_⟩ ?_
  · intro t ht
    dsimp only
    rw [hf₃' _ fun v hv => by have := hpre.P_lt v hv; omega]
    exact hout₂ t ht
  · intro x hx
    dsimp only
    by_cases hxP : ∃ v ∈ Vs, x = P + v
    · obtain ⟨v, hv, rfl⟩ := hxP
      obtain ⟨j, hj, hjv⟩ : ∃ j < len + 1, mem (vs + j) = v := by
        obtain ⟨j, hj, hjv⟩ := List.getElem_of_mem hv
        refine ⟨j, by omega, ?_⟩
        rw [hpre.verts j (by omega), List.getD_eq_getElem _ _ hj, hjv]
      have := hz₃ j hj
      rw [hvs₂ j hj, hjv] at this
      rw [this, hpre.zero v hv]
    · have hx' : ∀ v ∈ Vs, x ≠ P + v := fun v hv h => hxP ⟨v, hv, h⟩
      rw [hf₃' x hx', hframe₂ x (by omega), hcells x hx']
  · simp only [buildEraseContract, jumpContract, posFillContract, posClearContract,
      List.getD_cons_succ, List.getD_cons_zero, argsSize, Expr.size_reg, Expr.size_bin,
      Expr.size_const]
    omega

end MinCostFlow.HierPaths
