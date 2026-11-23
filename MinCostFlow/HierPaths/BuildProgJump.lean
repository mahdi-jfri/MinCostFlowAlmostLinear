module

public import MinCostFlow.HierPaths.BuildProgPosSpec

/-!
# Pass 2 of the shortcut as a procedure

`jumpProc`, called with `[ws, len, vs, P, out]`, runs pass 2 of the linear shortcut in memory.
The `len` edges of the walk `w` are the words at `ws`, its `len + 1` vertices
(`walkVerts E u w`) are the words at `vs`, and the cell `P + v` holds `posFill E u w Q v` for
each vertex `v` of the walk (what `posFillProc` leaves, `fillMem_eq_posFill`). From the current
vertex `cur`, the procedure reads `k = len − P(cur)`, writes edge `k` to the output, and goes on
from vertex `k + 1`; it stops when `P(cur) = 0`. It writes `erase E u w` at `out` and returns its
length (`jumpProc_meetsContract`), in at most `34 len + 20` steps: the value `P(cur)` drops at
each step (`posFill_index`).
-/

@[expose] public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

/-- The body of the loop: `r6 := len − P[cur]; out[r7] := ws[r6]; r7 := r7 + 1;
cur := vs[r6 + 1]`. -/
def jumpBody : Stmt :=
  .seq (.assign 6 (.bin .sub (.reg 1) (.load (.bin .add (.reg 3) (.reg 5)))))
    (.seq (.store (.bin .add (.reg 4) (.reg 7)) (.load (.bin .add (.reg 0) (.reg 6))))
      (.seq (.assign 7 (.bin .add (.reg 7) (.const 1)))
        (.assign 5 (.load (.bin .add (.bin .add (.reg 2) (.reg 6)) (.const 1))))))

/-- Pass 2: `cur := vs[0]; r7 := 0; while P[cur] ≠ 0: body; return r7`. -/
def jumpProc : Stmt :=
  .seq (.assign 5 (.load (.reg 2)))
    (.seq (.assign 7 (.const 0))
      (.seq (.loop (.load (.bin .add (.reg 3) (.reg 5))) jumpBody) (.ret (.reg 7))))

/-- What memory holds before pass 2, for the walk `w` from `u` and the array `posFill E u w Q`. -/
structure JumpPre (w : ℕ) (E : List (ℕ × ℕ)) (u : ℕ) (wk : List ℕ) (Q : ℕ → ℕ)
    (mem : ℕ → ℕ) (ws len vs P out : ℕ) : Prop where
  len_eq : len = wk.length
  edges : ∀ k < len, mem (ws + k) = wk.getD k 0
  verts : ∀ t ≤ len, mem (vs + t) = (walkVerts E u wk).getD t 0
  pos : ∀ v ∈ walkVerts E u wk, mem (P + v) = posFill E u wk Q v
  ws_lt : ws + len ≤ out
  vs_lt : vs + len + 1 ≤ out
  P_lt : ∀ v ∈ walkVerts E u wk, P + v < out
  out_lt : out + len < 2 ^ w
  hw : 1 < 2 ^ w

/-- The contract of `jumpProc` for the walk `wk` from `u` and the array `posFill E u wk Q`. -/
def jumpContract (w : ℕ) (E : List (ℕ × ℕ)) (u : ℕ) (wk : List ℕ) (Q : ℕ → ℕ) : Contract where
  pre args mem := ∃ ws len vs P out, args = [ws, len, vs, P, out] ∧
    JumpPre w E u wk Q mem ws len vs P out
  post args mem v mem' := ∃ ws len vs P out, args = [ws, len, vs, P, out] ∧
    v = (erase E u wk).length ∧ (∀ t < v, mem' (out + t) = (erase E u wk).getD t 0) ∧
    ∀ x, (x < out ∨ out + len ≤ x) → mem' x = mem x
  cost args _ := 34 * args.getD 1 0 + 20

end MinCostFlow.HierPaths

end

public section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.ExpanderDecomp

variable {w : ℕ} {E : List (ℕ × ℕ)} {u : ℕ} {wk : List ℕ} {Q : ℕ → ℕ}

theorem getD_mem_walkVerts {t : ℕ} (ht : t ≤ wk.length) :
    (walkVerts E u wk).getD t 0 ∈ walkVerts E u wk := by
  have : t < (walkVerts E u wk).length := by rw [length_walkVerts]; omega
  rw [List.getD_eq_getElem _ _ this]
  exact List.getElem_mem this

/-- The invariant of the loop. -/
def JumpInv (mem₀ : ℕ → ℕ) (ws len vs P out : ℕ) (st : State) : Prop :=
  st.regs 0 = ws ∧ st.regs 1 = len ∧ st.regs 2 = vs ∧ st.regs 3 = P ∧ st.regs 4 = out ∧
  ∃ i o, i ≤ len ∧ o ≤ i ∧ o ≤ (jumpRun E (posFill E u wk Q) u wk).length ∧
    st.regs 5 = (walkVerts E u wk).getD i 0 ∧ st.regs 7 = o ∧
    (∀ t < o, st.mem (out + t) = (jumpRun E (posFill E u wk Q) u wk).getD t 0) ∧
    (jumpRun E (posFill E u wk Q) u wk).drop o =
      jumpRun E (posFill E u wk Q) ((walkVerts E u wk).getD i 0) (wk.drop i) ∧
    ∀ x, (x < out ∨ out + o ≤ x) → st.mem x = mem₀ x

/-- **One step of the loop.** -/
theorem jump_step (p : Program) {mem₀ : ℕ → ℕ} {ws len vs P out : ℕ}
    (hpre : JumpPre w E u wk Q mem₀ ws len vs P out) (st : State)
    (hinv : JumpInv (E := E) (u := u) (wk := wk) (Q := Q) mem₀ ws len vs P out st)
    (hc : st.mem (P + st.regs 5) ≠ 0) :
    Triple w p (fun s => s = st) jumpBody
      (normalPost fun s' => JumpInv (E := E) (u := u) (wk := wk) (Q := Q) mem₀ ws len vs P out s' ∧
        s'.mem (P + s'.regs 5) < st.mem (P + st.regs 5))
      (fun _ => 29) := by
  obtain ⟨h0, h1, h2, h3, h4, i, o, hi, hoi, hoJ, h5, h7, hout, hdrop, hframe⟩ := hinv
  set Pf := posFill E u wk Q
  set Vs := walkVerts E u wk
  set J := jumpRun E Pf u wk
  set cur := Vs.getD i 0
  have hlen := hpre.len_eq
  have hcurV : cur ∈ Vs := getD_mem_walkVerts (by omega)
  have hPc_lt : P + cur < out := hpre.P_lt cur hcurV
  have hmemP : st.mem (P + cur) = Pf cur := by
    rw [hframe _ (Or.inl hPc_lt)]; exact hpre.pos cur hcurV
  obtain ⟨hle0, hcur0⟩ := posFill_index (E := E) u wk Q i (by omega)
  have hle : Pf cur ≤ wk.length - i := hle0
  have hcurk : Vs.getD (wk.length - Pf cur) 0 = cur := hcur0
  rw [h5] at hc
  have hpc : Pf cur ≠ 0 := by rw [← hmemP]; exact hc
  set k := len - Pf cur with hk
  have hklt : k < len := by omega
  have hik : i ≤ k := by omega
  have hidx := jumpRun_index (E := E) u wk Q (i := i) (by omega)
  have hpc0 : ¬ posFill E u wk Q ((walkVerts E u wk).getD i 0) = 0 := hpc
  simp only [hpc0, ↓reduceIte] at hidx
  rw [← hdrop] at hidx
  have hk' : wk.length - Pf cur = k := by omega
  rw [hk'] at hidx
  -- the values read
  have hwsk : st.mem (ws + k) = wk.getD k 0 := by
    rw [hframe _ (Or.inl (by have := hpre.ws_lt; omega))]; exact hpre.edges k hklt
  have hvsk : st.mem (vs + k + 1) = Vs.getD (k + 1) 0 := by
    rw [hframe _ (Or.inl (by have := hpre.vs_lt; omega))]; exact hpre.verts (k + 1) (by omega)
  have hJo : J.getD o 0 = wk.getD k 0 := by
    have := congrArg (fun l => l.getD 0 0) hidx
    simp only [List.getD_cons_zero] at this
    rw [← this]
    simp [List.getD_eq_getElem?_getD]
  have hol : o < len := by omega
  have hkq : k + st.mem (P + cur) = len := by rw [hmemP]; omega
  have hw := hpre.hw
  have hout_lt := hpre.out_lt
  -- the four statements
  set st1 : State := { st with regs := Function.update st.regs 6 k }
  set st2 : State := { st1 with mem := Function.update st1.mem (out + o) (wk.getD k 0) }
  set st3 : State := { st2 with regs := Function.update st2.regs 7 (o + 1) }
  set st4 : State := { st3 with regs := Function.update st3.regs 5 (Vs.getD (k + 1) 0) }
  have t1 : Triple w p (fun s => s = st) (.assign 6 (.bin .sub (.reg 1) (.load (.bin .add (.reg 3) (.reg 5)))))
      (normalPost fun s => s = st1) (fun _ => 7) := by
    refine Triple.assign (val := fun _ => k) ?_ ?_
    · intro s hs; subst hs
      have : P + cur < 2 ^ w := by omega
      have hlw : len < 2 ^ w := by omega
      simp [Expr.eval, BinOp.eval, h1, h3, h5, this]
      have hv : len - s.mem (P + cur) = k := by omega
      have hkw : k < 2 ^ w := by omega
      simp only [hv, hkw, ite_true]
    · intro s hs; subst hs; rfl
  have t2 : Triple w p (fun s => s = st1)
      (.store (.bin .add (.reg 4) (.reg 7)) (.load (.bin .add (.reg 0) (.reg 6))))
      (normalPost fun s => s = st2) (fun _ => 8) := by
    refine Triple.store (addr := fun _ => out + o) (val := fun _ => wk.getD k 0) ?_ ?_ ?_
    · intro s hs; subst hs
      have : out + o < 2 ^ w := by omega
      simp [st1, Expr.eval, BinOp.eval, h4, h7, this]
    · intro s hs; subst hs
      have : ws + k < 2 ^ w := by have := hpre.ws_lt; omega
      simp [st1, Expr.eval, BinOp.eval, h0, this, hwsk]
    · intro s hs; subst hs; rfl
  have t3 : Triple w p (fun s => s = st2) (.assign 7 (.bin .add (.reg 7) (.const 1)))
      (normalPost fun s => s = st3) (fun _ => 4) := by
    refine Triple.assign (val := fun _ => o + 1) ?_ ?_
    · intro s hs; subst hs
      have : o + 1 < 2 ^ w := by omega
      have h1w : 1 < 2 ^ w := hw
      simp [st2, st1, Expr.eval, BinOp.eval, h7, this, h1w]
    · intro s hs; subst hs; rfl
  have t4 : Triple w p (fun s => s = st3)
      (.assign 5 (.load (.bin .add (.bin .add (.reg 2) (.reg 6)) (.const 1))))
      (normalPost fun s => s = st4) (fun _ => 7) := by
    refine Triple.assign (val := fun _ => Vs.getD (k + 1) 0) ?_ ?_
    · intro s hs; subst hs
      have hb : vs + k + 1 < 2 ^ w := by have := hpre.vs_lt; omega
      have hb' : vs + k < 2 ^ w := by omega
      have hne : vs + k + 1 ≠ out + o := by have := hpre.vs_lt; omega
      simp [st3, st2, st1, Expr.eval, BinOp.eval, h2, hb, hb', hw, Function.update_of_ne hne,
        hvsk]
    · intro s hs; subst hs; rfl
  have hall := Triple.seq_normal_const t1 (Triple.seq_normal_const t2 (Triple.seq_normal_const t3 t4))
  refine hall.conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o' s' hpost
  cases o' with
  | returned _ => exact False.elim hpost
  | normal =>
    simp only [normalPost] at hpost
    subst hpost
    have hnV : Vs.getD (k + 1) 0 ∈ Vs := getD_mem_walkVerts (by omega)
    have hPn : P + Vs.getD (k + 1) 0 < out := hpre.P_lt _ hnV
    obtain ⟨hlen1, _⟩ := posFill_index (E := E) u wk Q (k + 1) (by omega)
    have hmem4 : st4.mem (P + Vs.getD (k + 1) 0) = Pf (Vs.getD (k + 1) 0) := by
      show Function.update st.mem (out + o) (wk.getD k 0) (P + Vs.getD (k + 1) 0) = _
      rw [Function.update_of_ne (by omega), hframe _ (Or.inl hPn)]
      exact hpre.pos _ hnV
    have hJlen : o + 1 ≤ J.length := by
      have := congrArg List.length hidx
      simp only [List.length_drop, List.length_cons] at this
      omega
    refine ⟨⟨by simp [st4, st3, st2, st1, h0], by simp [st4, st3, st2, st1, h1],
      by simp [st4, st3, st2, st1, h2], by simp [st4, st3, st2, st1, h3],
      by simp [st4, st3, st2, st1, h4], k + 1, o + 1, by omega, by omega, hJlen,
      by simp only [st4, Function.update_self]; rfl, by simp [st4, st3], ?_, ?_, ?_⟩, ?_⟩
    · intro t ht
      show Function.update st.mem (out + o) (wk.getD k 0) (out + t) = _
      by_cases hto : t = o
      · subst hto; rw [Function.update_self, hJo]
      · rw [Function.update_of_ne (by omega)]; exact hout t (by omega)
    · rw [← List.drop_drop, hidx]; rfl
    · intro x hx
      show Function.update st.mem (out + o) (wk.getD k 0) x = _
      rw [Function.update_of_ne (by omega)]
      exact hframe x (by omega)
    · have e1 : st4.regs 5 = Vs.getD (k + 1) 0 := by simp only [st4, Function.update_self]
      rw [e1, h5, hmem4, hmemP]
      have hlen1' : Pf (Vs.getD (k + 1) 0) ≤ wk.length - (k + 1) := hlen1
      omega

/-- The loop of pass 2. -/
theorem jump_loop (p : Program) {mem₀ : ℕ → ℕ} {ws len vs P out : ℕ}
    (hpre : JumpPre w E u wk Q mem₀ ws len vs P out) :
    Triple w p (JumpInv (E := E) (u := u) (wk := wk) (Q := Q) mem₀ ws len vs P out)
      (.loop (.load (.bin .add (.reg 3) (.reg 5))) jumpBody)
      (normalPost fun st => JumpInv (E := E) (u := u) (wk := wk) (Q := Q) mem₀ ws len vs P out st ∧
        st.mem (P + st.regs 5) = 0)
      (fun st => (4 + 29 + 1) * st.mem (P + st.regs 5) + 4 + 1) := by
  refine Triple.loop_const (m := fun st => st.mem (P + st.regs 5))
    (condVal := fun st => st.mem (P + st.regs 5)) 29 ?_ ?_ ?_ ?_
  · intro st hinv
    obtain ⟨_, _, _, h3, _, i, o, hi, _, _, h5, _⟩ := hinv
    have hV : (walkVerts E u wk).getD i 0 ∈ walkVerts E u wk :=
      getD_mem_walkVerts (by have := hpre.len_eq; omega)
    have hlt : P + st.regs 5 < 2 ^ w := by
      rw [h5]; have := hpre.P_lt _ hV; have := hpre.out_lt; omega
    have hlt' : P + (walkVerts E u wk).getD i 0 < 2 ^ w := by rw [← h5]; exact hlt
    simp only [Expr.eval, BinOp.eval, h3, h5, hlt', ↓reduceIte, Option.map_some]
  · intro st hinv hc
    exact ⟨hinv, hc⟩
  · intro st _ hc
    omega
  · intro st hinv hc
    refine (jump_step p hpre st hinv hc).conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
    intro o s' h
    cases o with
    | returned _ => exact False.elim h
    | normal => exact h

/-- **`jumpProc` meets its contract**: it writes `erase E u wk` at `out` and returns its
length. -/
theorem jumpProc_meetsContract {p : Program} {f : ℕ} (hp : p.procs[f]? = some jumpProc) :
    MeetsContract w p f (jumpContract w E u wk Q) := by
  refine meetsContract_of_runs hp fun args mem pos ω hwords hpre => ?_
  rcases hpre with ⟨ws, len, vs, P, out, rfl, hpre⟩
  have hlen := hpre.len_eq
  have hw := hpre.hw
  refine runs_start_le ?_
  dsimp only [jumpProc]
  have hv0 : mem vs = (walkVerts E u wk).getD 0 0 := by
    have := hpre.verts 0 (Nat.zero_le _); simpa using this
  refine runs_seq_assign_le (v := (walkVerts E u wk).getD 0 0) ?_ ?_
  · simp [Expr.eval, startState, hv0]
  refine runs_seq_assign_le (v := 0) (by eval_expr) ?_
  set st0 : State := { { startState [ws, len, vs, P, out] mem pos with
      regs := Function.update (startState [ws, len, vs, P, out] mem pos).regs 5
        ((walkVerts E u wk).getD 0 0) } with
      regs := Function.update (Function.update (startState [ws, len, vs, P, out] mem pos).regs 5
        ((walkVerts E u wk).getD 0 0)) 7 0 }
  have hu0 : (walkVerts E u wk).getD 0 0 = u := by rw [walkVerts_eq_cons]; rfl
  have hinv0 : JumpInv (E := E) (u := u) (wk := wk) (Q := Q) mem ws len vs P out st0 := by
    refine ⟨by simp [st0, startState], by simp [st0, startState], by simp [st0, startState],
      by simp [st0, startState], by simp [st0, startState], 0, 0, Nat.zero_le _, le_rfl,
      Nat.zero_le _, by simp [st0], by simp [st0], fun t ht => absurd ht (Nat.not_lt_zero _),
      ?_, fun x _ => rfl⟩
    rw [hu0]; simp
  refine runs_seq_triple_le (jump_loop p hpre) hinv0 ?_
  intro st₁ ⟨hinv, hz⟩
  obtain ⟨_, _, _, _, _, i, o, hi, hoi, hoJ, h5, h7, hout, hdrop, hframe⟩ := hinv
  have hV : (walkVerts E u wk).getD i 0 ∈ walkVerts E u wk := getD_mem_walkVerts (by omega)
  have hP0 : posFill E u wk Q ((walkVerts E u wk).getD i 0) = 0 := by
    rw [← hpre.pos _ hV, ← hframe _ (Or.inl (hpre.P_lt _ hV)), ← h5]; exact hz
  have hidx := jumpRun_index (E := E) u wk Q (i := i) (by omega)
  simp only [hP0, ↓reduceIte] at hidx
  rw [← hdrop] at hidx
  have hJo : (jumpRun E (posFill E u wk Q) u wk).length = o := by
    have := congrArg List.length hidx
    simp only [List.length_drop, List.length_nil] at this
    omega
  have herase := jumpRun_eq_erase (E := E) u wk Q
  refine runs_ret_le (v := o) (by simp [Expr.eval, h7]) ⟨ws, len, vs, P, out, rfl, ?_, ?_, ?_⟩ ?_
  · show o = _
    rw [← herase, hJo]
  · intro t ht
    have ht' : t < o := ht
    rw [hout t ht', herase]
  · intro x hx
    exact hframe x (by omega)
  · have hm : st0.mem (P + st0.regs 5) ≤ len := by
      have : st0.regs 5 = u := by
        simp only [st0, Function.update_of_ne (show (5 : ℕ) ≠ 7 by decide), Function.update_self]
        exact hu0
      rw [this]
      have hu : u ∈ walkVerts E u wk := mem_walkVerts_self u wk
      have h1 : st0.mem (P + u) = posFill E u wk Q u := hpre.pos u hu
      rw [h1]
      have := (posFill_index (E := E) u wk Q 0 (Nat.zero_le _)).1
      rw [hu0] at this
      omega
    simp only [jumpContract, List.getD_cons_succ, List.getD_cons_zero, Expr.size_reg,
      Expr.size_load, Expr.size_const]
    omega

end MinCostFlow.HierPaths
