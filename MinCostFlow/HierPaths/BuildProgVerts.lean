module

public import MinCostFlow.HierPaths.BuildProgJump

/-!
# The vertices of a walk

The linear shortcut (`buildEraseProc`) reads the vertices of the walk from a list in memory. The
router returns only the edges of the walk, so the builder first lists the vertices.
`vertsProc`, called with `[ws, len, u, ends, vs]`, where the walk `wk` from `u` is the words
`ws, …, ws + len − 1` and edge `j` has its ends at `ends + 2 j` and `ends + 2 j + 1`, writes
`walkVerts E u wk` at `vs` and changes no other cell (`vertsProc_meetsContract`). The next vertex
is computed without a branch: it is `b` if the first end `a` of the edge is the current vertex,
and `a` otherwise, which is `[a = cur] · b + (1 − [a = cur]) · a`. The cost is `56 len + 40`.
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The address of the first end of the edge `mem[ws + r6]`. -/
def endAddr : Expr :=
  .bin .add (.reg 3) (.bin .mul (.const 2) (.load (.bin .add (.reg 0) (.reg 6))))

/-- One step: `r7 := a; r8 := b; r9 := [r7 = r5]; r5 := r9 · r8 + (1 − r9) · r7;
mem[vs + r6 + 1] := r5`. -/
def vertsBody : Stmt :=
  .seq (.assign 7 (.load endAddr))
    (.seq (.assign 8 (.load (.bin .add endAddr (.const 1))))
      (.seq (.assign 9 (.bin .eq (.reg 7) (.reg 5)))
        (.seq (.assign 5 (.bin .add (.bin .mul (.reg 9) (.reg 8))
            (.bin .mul (.bin .sub (.const 1) (.reg 9)) (.reg 7))))
          (.store (.bin .add (.bin .add (.reg 4) (.reg 6)) (.const 1)) (.reg 5)))))

/-- `mem[vs] := u; r5 := u; for r6 in [0, len): vertsBody`; return `0`. -/
def vertsProc : Stmt :=
  .seq (.store (.reg 4) (.reg 2))
    (.seq (.assign 5 (.reg 2)) (.seq (forRange 6 (.const 0) (.reg 1) vertsBody) (.ret (.const 0))))

/-- What memory holds before `vertsProc`. -/
structure VertsPre (w : ℕ) (E : List (ℕ × ℕ)) (u : ℕ) (wk : List ℕ) (mem : ℕ → ℕ)
    (ws len ends vs : ℕ) : Prop where
  len_eq : len = wk.length
  edges : ∀ k < len, mem (ws + k) = wk.getD k 0
  fst : ∀ k < len, mem (ends + 2 * wk.getD k 0) = (edgeAt E (wk.getD k 0)).1
  snd : ∀ k < len, mem (ends + 2 * wk.getD k 0 + 1) = (edgeAt E (wk.getD k 0)).2
  ends_lt : ∀ k < len, ends + 2 * wk.getD k 0 + 1 < vs
  ends_word : ∀ k < len, (edgeAt E (wk.getD k 0)).1 < 2 ^ w ∧ (edgeAt E (wk.getD k 0)).2 < 2 ^ w
  ws_lt : ws + len ≤ vs
  vs_lt : vs + len + 1 < 2 ^ w
  hw : 1 < 2 ^ w

/-- The contract of `vertsProc`. -/
def vertsContract (w : ℕ) (E : List (ℕ × ℕ)) (u : ℕ) (wk : List ℕ) : Contract where
  pre args mem := ∃ ws len ends vs, args = [ws, len, u, ends, vs] ∧
    VertsPre w E u wk mem ws len ends vs
  post args mem _ mem' := ∃ ws len ends vs, args = [ws, len, u, ends, vs] ∧
    (∀ t ≤ len, mem' (vs + t) = (walkVerts E u wk).getD t 0) ∧
    ∀ x, (x < vs ∨ vs + len + 1 ≤ x) → mem' x = mem x
  cost args _ := 56 * args.getD 1 0 + 40

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

variable {w : ℕ} {E : List (ℕ × ℕ)} {u : ℕ} {wk : List ℕ}

/-- The branch-free form of `otherEnd`. -/
theorem otherEnd_formula (E : List (ℕ × ℕ)) (j c : ℕ) :
    (if (edgeAt E j).1 = c then 1 else 0) * (edgeAt E j).2 +
      (1 - if (edgeAt E j).1 = c then 1 else 0) * (edgeAt E j).1 = otherEnd E j c := by
  unfold otherEnd
  split_ifs <;> simp

/-- The loop of `vertsProc`. -/
theorem verts_triple (p : Program) {mem₀ : ℕ → ℕ} {ws len ends vs : ℕ}
    (hpre : VertsPre w E u wk mem₀ ws len ends vs) :
    Triple w p (fun st => st.regs 0 = ws ∧ st.regs 1 = len ∧ st.regs 3 = ends ∧
        st.regs 4 = vs ∧ st.regs 5 = u ∧ st.mem = Function.update mem₀ vs u)
      (forRange 6 (.const 0) (.reg 1) vertsBody)
      (normalPost fun st' => (∀ t ≤ len, st'.mem (vs + t) = (walkVerts E u wk).getD t 0) ∧
        ∀ x, (x < vs ∨ vs + len + 1 ≤ x) → st'.mem x = mem₀ x)
      (fun _ => 56 * len + 7) := by
  have hw := hpre.hw
  have hvl := hpre.vs_lt
  have hwl := hpre.ws_lt
  set V := walkVerts E u wk
  have hV0 : V.getD 0 0 = u := by cases wk <;> rfl
  have hV0' : V[0]?.getD 0 = u := by rw [← List.getD_eq_getElem?_getD]; exact hV0
  have hloop := Triple.forRange_const (p := p) (r := 6) (lo := .const 0) (hi := .reg 1)
    (body := vertsBody)
    (P := fun st => st.regs 0 = ws ∧ st.regs 1 = len ∧ st.regs 3 = ends ∧
        st.regs 4 = vs ∧ st.regs 5 = u ∧ st.mem = Function.update mem₀ vs u)
    (Inv := fun i st =>
      st.regs 0 = ws ∧ st.regs 1 = len ∧ st.regs 3 = ends ∧ st.regs 4 = vs ∧ st.regs 6 = i ∧
      st.regs 5 = V.getD i 0 ∧
      (∀ t ≤ i, st.mem (vs + t) = V.getD t 0) ∧
      (∀ x, (x < vs ∨ vs + i + 1 ≤ x) → st.mem x = mem₀ x))
    47 0 len (Nat.zero_le _) hw (fun _ => by omega)
    (fun st ⟨h0, h1, h3, h4, h5, hm⟩ => by
      refine ⟨by eval_expr, ?_⟩
      refine ⟨by simp [h0], by simp [h1], by simp [h3], by simp [h4], by simp,
        by simp [h5, hV0'], fun t ht => ?_, fun x hx => ?_⟩
      · rw [Nat.le_zero.mp ht]; simp [hm, hV0']
      · simp only [hm]; rw [Function.update_of_ne (by omega)])
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => by
      have h1 : st.regs 1 = len := hi.2.1
      simp [Expr.eval, h1])
    (fun i _ hilt => by
      intro st ω ⟨h0, h1, h3, h4, h6, h5, hz, hf⟩
      have hlen := hpre.len_eq
      have h2 : 2 < 2 ^ w := by omega
      set j := wk.getD i 0 with hj
      have hwsi : st.mem (ws + i) = j := by
        rw [hf _ (Or.inl (by omega))]; exact hpre.edges i hilt
      have hel := hpre.ends_lt i hilt
      have ha : st.mem (ends + 2 * j) = (edgeAt E j).1 := by
        rw [hf _ (Or.inl (by omega))]; exact hpre.fst i hilt
      have hb : st.mem (ends + 2 * j + 1) = (edgeAt E j).2 := by
        rw [hf _ (Or.inl (by omega))]; exact hpre.snd i hilt
      obtain ⟨haw, hbw⟩ : (edgeAt E j).1 < 2 ^ w ∧ (edgeAt E j).2 < 2 ^ w :=
        hpre.ends_word i hilt
      have hwsw : ws + i < 2 ^ w := by omega
      have h2j : 2 * j < 2 ^ w := by omega
      have hej : ends + 2 * j < 2 ^ w := by omega
      have hej1 : ends + 2 * j + 1 < 2 ^ w := by omega
      have hnext : V.getD (i + 1) 0 = otherEnd E j (V.getD i 0) :=
        walkVerts_succ u wk i (by omega)
      have hnw : otherEnd E j (V.getD i 0) < 2 ^ w := by
        unfold otherEnd; split_ifs <;> assumption
      have hvi : vs + i + 1 < 2 ^ w := by omega
      have hvi' : vs + i < 2 ^ w := by omega
      obtain ⟨o, st', c', hr, hq, hc⟩ : ∃ o st' c', Runs w p ω vertsBody st o st' c' ∧
          normalPost (fun st₁ => (fun i st =>
            st.regs 0 = ws ∧ st.regs 1 = len ∧ st.regs 3 = ends ∧ st.regs 4 = vs ∧
            st.regs 6 = i ∧ st.regs 5 = V.getD i 0 ∧
            (∀ t ≤ i, st.mem (vs + t) = V.getD t 0) ∧
            (∀ x, (x < vs ∨ vs + i + 1 ≤ x) → st.mem x = mem₀ x)) (i + 1)
              { st₁ with regs := Function.update st₁.regs 6 (i + 1) } ∧ st₁.regs 6 = i) o st' ∧
          0 + c' ≤ 47 := by
        dsimp only [vertsBody]
        refine runs_seq_assign_le (v := (edgeAt E j).1) (by
          simp [endAddr, Expr.eval, BinOp.eval, h0, h3, h6, hwsi, hwsw, h2, h2j, hej, ha]) ?_
        refine runs_seq_assign_le (v := (edgeAt E j).2) (by
          simp [endAddr, Expr.eval, BinOp.eval, Function.update, h0, h3, h6, hwsi, hwsw, h2,
            h2j, hej, hej1, hb, hw]) ?_
        refine runs_seq_assign_le (v := if (edgeAt E j).1 = V.getD i 0 then 1 else 0) (by
          simp only [Expr.eval, Function.update]
          by_cases hac : (edgeAt E j).1 = V[i]?.getD 0
          · simp [hac, h5, BinOp.eval, hw, List.getD_eq_getElem?_getD]
          · simp [hac, h5, BinOp.eval, List.getD_eq_getElem?_getD]) ?_
        refine runs_seq_assign_le (v := otherEnd E j (V.getD i 0)) (by
          simp only [Expr.eval, Function.update]
          by_cases hac : (edgeAt E j).1 = V[i]?.getD 0
          · simp [hac, BinOp.eval, hw, hbw, otherEnd, List.getD_eq_getElem?_getD]
          · simp [hac, BinOp.eval, hw, haw, otherEnd, List.getD_eq_getElem?_getD]) ?_
        refine ⟨.normal, _, _, runs_store_iff.mpr ⟨vs + i + 1, otherEnd E j (V.getD i 0), by
          simp [Expr.eval, Function.update, h4, h6, hvi, hvi', hw], by
          simp [Expr.eval, Function.update], rfl, rfl, rfl⟩, ?_, ?_⟩
        · refine ⟨⟨by simp [Function.update, h0], by simp [Function.update, h1],
            by simp [Function.update, h3], by simp [Function.update, h4], by simp,
            by dsimp only; rw [Function.update_of_ne (by decide), Function.update_self]
               exact hnext.symm, ?_, ?_⟩, by simp [Function.update, h6]⟩
          · intro t ht
            dsimp only
            rcases Nat.lt_or_ge t (i + 1) with hti | hti
            · rw [Function.update_of_ne (by omega)]; exact hz t (by omega)
            · rw [show t = i + 1 by omega, ← Nat.add_assoc, Function.update_self, hnext]
          · intro x hx
            dsimp only
            rw [Function.update_of_ne (by omega)]
            exact hf x (by omega)
        · simp [endAddr, Expr.size]
      exact ⟨o, st', c', hr, hq, show c' ≤ 47 by omega⟩)
  refine hloop.conseq (fun _ h => h) ?_ ?_
  · intro o st' hpost
    cases o with
    | returned u => exact False.elim hpost
    | normal =>
      obtain ⟨_, _, _, _, _, _, hz, hf⟩ := hpost
      exact ⟨hz, hf⟩
  · intro _ _
    simp only [Nat.sub_zero, Expr.size_const, Expr.size_reg]
    omega

/-- **`vertsProc` lists the vertices of the walk.** -/
theorem vertsProc_meetsContract {p : Program} {f : ℕ} (hp : p.procs[f]? = some vertsProc) :
    MeetsContract w p f (vertsContract w E u wk) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨ws, len, ends, vs, rfl, hpre⟩
  have hvl := hpre.vs_lt
  refine runs_start_le ?_
  dsimp only [vertsProc]
  refine runs_seq_store_le (x := vs) (v := u) (by simp [Expr.eval, startState])
    (by simp [Expr.eval, startState]) ?_
  refine runs_seq_assign_le (v := u) (by simp [Expr.eval, startState]) ?_
  refine runs_seq_triple_le (verts_triple p hpre)
    ⟨by simp [startState], by simp [startState], by simp [startState], by simp [startState],
      by simp [Function.update], rfl⟩ ?_
  intro st₁ ⟨hz, hf⟩
  refine runs_ret_le (v := 0) (by eval_expr) ⟨ws, len, ends, vs, rfl, hz, fun x hx => ?_⟩ ?_
  · rw [hf x hx]
  · simp only [vertsContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_const,
      Expr.size_reg]
    omega

end MinCostFlow.HierPaths
