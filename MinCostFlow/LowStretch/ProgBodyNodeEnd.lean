module

public import MinCostFlow.LowStretch.ProgBodyNode
public import MinCostFlow.LowStretch.ProgRecLoop

/-!
# The end of the node part

`nodeEnd` sets register `63` to `hS + 16`, calls the child step there with the petal block at
`hS`, writes the four words of `wr4` at `h` and returns. When the memory meets `ChildPre`,
`MeetsChild` gives the run of the child step, and `bodyPost_of_childPost` turns its `ChildPost`
into `BodyPost` (`nodeEnd_runs`).
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

/-- **The run of the end of the node part**, given a run of the child step on the memory of the
state: it ends with the four words of `wr4` written over the memory that the child step leaves,
within `60` steps more than the child step. -/
theorem nodeEnd_runs_of {w : ℕ} {p : Program} {ω : ℕ → Bool} {bK : ℕ} {body : Stmt}
    (hb : p.procs[bK]? = some body) {GB RB h hS PT n0 : ℕ} {st : State} {o1 : Outcome}
    {st1 : State} {cost1 : ℕ}
    (hr1 : Runs w p ω body (startState [GB, RB, hS, hS + 16] st.mem st.pos) o1 st1 cost1)
    (r37 : st.regs 37 = PT) (r57 : st.regs 57 = hS) (r58 : st.regs 58 = n0)
    (r60 : st.regs 60 = GB) (r61 : st.regs 61 = RB) (r62 : st.regs 62 = h)
    (hw : hS + 16 < 2 ^ w) (hnP : n0 + 1 < 2 ^ w) (hh : h + 4 ≤ hS + 16) :
    ∃ o st' c', Runs w p ω (nodeEnd bK) st o st' c' ∧
      st'.mem = wr4 st1.mem h (n0 + 1) (hS + 16) o1.value PT ∧ c' ≤ cost1 + 60 := by
  refine runs_start_le ?_
  unfold nodeEnd
  refine runs_seq_assign_le (v := hS + 16)
    (Expr.eval_add (Expr.eval_reg_of_eq r57) (Expr.eval_const (by omega)) hw) ?_
  refine runs_seq_call_runs (vs := [GB, RB, hS, hS + 16])
    (Post := fun c v M => c = cost1 ∧ v = o1.value ∧ M = st1.mem)
    ⟨body, hb, o1, st1, cost1, hr1, rfl, rfl, rfl⟩
    (by simp [evalArgs, Expr.eval, r57, r60, r61]) ?_
  rintro c v M pos' ⟨rfl, rfl, rfl⟩
  have q62 : ∀ (r : ℕ → ℕ), r = Function.update (Function.update st.regs 63 (hS + 16)) 59
      o1.value → r 62 = h := fun r e => by subst e; simp [r62]
  refine runs_seq_store_le (x := h) (v := n0 + 1)
    (Expr.eval_reg_of_eq (q62 _ rfl))
    (Expr.eval_add (Expr.eval_reg_of_eq (v := n0) (by simp [r58]))
      (Expr.eval_const (by omega)) hnP) ?_
  refine runs_seq_store_le (x := h + 1) (v := hS + 16)
    (Expr.eval_add (Expr.eval_reg_of_eq (q62 _ rfl)) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := h + 2) (v := o1.value)
    (Expr.eval_add (Expr.eval_reg_of_eq (q62 _ rfl)) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp)) ?_
  refine runs_seq_store_le (x := h + 3) (v := PT)
    (Expr.eval_add (Expr.eval_reg_of_eq (q62 _ rfl)) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by simp [r37])) ?_
  refine runs_ret_le (v := 0) (Expr.eval_const (by omega)) ?_ ?_
  · simp only
    rw [wr4_eq]
  · simp only [Expr.size, argsSize]
    omega

/-- **The end of the node part.** From a state whose memory meets `ChildPre` at `hS + 16` with
the petal block at `hS`, with the arguments, `hS`, the number of petals and the portal address
in their registers, the end runs and leaves `BodyPost`, for the cost `K` spent before it, when
`hfit` bounds the total cost and the heap for every choice of the children. -/
theorem nodeEnd_runs {w A : ℕ} {p : Program} {ω : ℕ → Bool} {bK : ℕ} (hK : MeetsChild w p bK)
    {T : KT} {G : PG} {P : Par} {c : Cl} {R : Rec} {D : Cl.Dec} {GB RB h hS PT K : ℕ}
    {mem : ℕ → ℕ} {st : State}
    (hpre : ClPre w A T G P c R GB RB h mem) (hX : 2 ≤ c.X.card) (hD : c.DecOk G P D)
    (hsat : ∀ k < D.nch, T.Sat G c.θ (c.raw G D k).X)
    (hcp : ChildPre w T G P c R D GB RB hS (hS + 16) st.mem)
    (r37 : st.regs 37 = PT) (r57 : st.regs 57 = hS) (r58 : st.regs 58 = D.ps.length)
    (r60 : st.regs 60 = GB) (r61 : st.regs 61 = RB) (r62 : st.regs 62 = h)
    (hlow : ∀ a < h, st.mem a = mem a) (hPT : h + 4 ≤ PT) (hPT2 : PT + D.ps.length ≤ hS + 16)
    (hh : h + 4 ≤ hS + 16) (hport : ∀ j < D.ps.length, st.mem (PT + j) = D.portal j)
    (hw : hS + 16 < 2 ^ w)
    (hfit : ∀ (cs : ℕ → Cl) (cost : ℕ), cost ≤ childCost T G P c R D cs (GlobL.read mem GB).J →
      K + cost + 100 ≤ bodyShare A T G P c R D cs + D.nch * kidCost w G.n ∧
      hS + 16 + ((GlobL.read mem GB).J + 1) * childCost T G P c R D cs (GlobL.read mem GB).J ≤
        h + 4 + ((GlobL.read mem GB).J + 1) *
          (bodyShare A T G P c R D cs + D.nch * kidCost w G.n)) :
    ∃ o st' c', Runs w p ω (nodeEnd bK) st o st' c' ∧
      BodyPost w A T G P c R (GlobL.read mem GB) h mem st'.mem (K + c' + 20) := by
  have hE : GlobL.read st.mem GB = GlobL.read mem GB := GlobL.read_congr fun i hi => by
    have := hpre.below (GB, 21) (by simp [recRegs]); simp only at this
    exact hlow _ (by omega)
  have hnP : D.ps.length + 1 < 2 ^ w := by omega
  obtain ⟨body, hb, o1, st1, cost1, hr1, hpost⟩ :=
    hK T G P c R D GB RB hS (hS + 16) st.mem st.pos ω hcp
  obtain ⟨o, st', c', hr, hm, hc⟩ := nodeEnd_runs_of hb hr1 r37 r57 r58 r60 r61 r62 hw hnP hh
  refine ⟨o, st', c', hr, ?_⟩
  rw [hm]
  refine bodyPost_of_childPost hpre hX hD hsat hlow (by omega) hPT hPT2 hport hE hpost
    fun cs hcs => ?_
  obtain ⟨f1, f2⟩ := hfit cs cost1 hcs
  exact ⟨by omega, f2⟩

end MinCostFlow.LowStretch
