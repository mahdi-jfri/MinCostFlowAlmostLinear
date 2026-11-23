module

public import MinCostFlow.LastLevelProgram.AncestorRow
import WordRAM.Tactic

/-!
# Building the binary lifting table

The stretch pass uses a contiguous table of parent jumps, beginning
with the parent row. Each outer iteration doubles the previous
row by invoking the verified single-row procedure.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Arguments to the row call at the current table level. -/
def ancestorTableArgs : List Expr :=
  [.bin .add (.reg 0) (.bin .mul (.reg 3) (.reg 1)),
   .bin .add (.reg 0) (.bin .mul (.bin .add (.reg 3) (.const 1)) (.reg 1)),
   .reg 1]

/-- Arguments are the parent row base, vertex count, and number of
additional rows. -/
def ancestorTableLoop (row : ℕ) : Stmt :=
  forRange 3 (.const 0) (.reg 2) (.call 4 row ancestorTableArgs)

/-- Build all the requested levels of the jump table. Each additional
level costs only a linear pass over the compact vertex range. -/
theorem ancestorTableLoop_triple {w row : ℕ} {p : Program}
    (hp : p.procs[row]? = some ancestorRowBody) (mem : ℕ → ℕ)
    (pos base n levels : ℕ) (parent : ℕ → ℕ)
    (hw : 1 < 2^w) (hlevels : levels < 2^w)
    (hroom : base + (levels+1)*n < 2^w)
    (hparent : ∀ v < n, parent v < n ∧ mem (base+v) = parent v) :
    Triple w p (fun st => st = startState [base,n,levels] mem pos)
      (ancestorTableLoop row)
      (normalPost fun st =>
        (∀ k ≤ levels, ∀ v < n, st.mem (base+k*n+v) = ancestorJump parent k v) ∧
        (∀ a, a < base+n ∨ base+(levels+1)*n ≤ a → st.mem a = mem a))
      (fun _ => (20*n+40)*levels+7) := by
  let Inv := fun k (st : State) =>
    st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 = levels ∧ st.regs 3 = k ∧
    (∀ j ≤ k, ∀ v < n, st.mem (base+j*n+v) = ancestorJump parent j v) ∧
    (∀ a, a < base+n ∨ base+(k+1)*n ≤ a → st.mem a = mem a)
  have loop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 2)
    (body := .call 4 row ancestorTableArgs) (Inv := Inv)
    (P := fun st => st = startState [base,n,levels] mem pos)
    (20*n+31) 0 levels (Nat.zero_le _) hw (fun _ => hlevels)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, ?_⟩
      refine ⟨?_,?_,?_,?_,?_,fun _ _ => rfl⟩
      · simp [startState]
      · simp [startState]
      · simp [startState]
      · simp
      · intro j hj v hv
        have he : j = 0 := Nat.eq_zero_of_le_zero hj
        subst j
        simpa [ancestorJump, startState] using (hparent v hv).2)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ st _ _ h => by
      have hr : st.regs 2 = levels := h.2.2.1
      eval_expr)
    (fun k _ hk => by
      intro st ω ⟨h0,h1,h2,h3,hdone,hframe⟩
      let src := base+k*n
      let dst := base+(k+1)*n
      have hs : src+n = dst := by simp [src,dst,Nat.succ_mul,Nat.add_assoc]
      have hd : dst+n < 2^w := by
        have hle := Nat.mul_le_mul_right n (show k+1+1 ≤ levels+1 by omega)
        rw [Nat.succ_mul] at hle
        dsimp [dst]
        omega
      have hsrc : src+n < 2^w := by omega
      have hsmall : k*n < 2^w := by dsimp [src] at hsrc; omega
      have hlarge : (k+1)*n < 2^w := by dsimp [dst] at hd; omega
      have hkWord : k+1 < 2^w := by omega
      have hwne : w ≠ 0 := by
        intro he
        subst w
        simp at hw
      have hargs : evalArgs w st ancestorTableArgs = some [src,dst,n] := by
        simp [ancestorTableArgs,evalArgs,Expr.eval,h0,h1,h3,src,dst,hwne,hsmall,hlarge,hkWord,
          show base+k*n < 2^w from (show src < 2^w by omega),
          show base+(k+1)*n < 2^w from (show dst < 2^w by omega)]
      have hwords : ∀ x ∈ [src,dst,n], x < 2^w := by
        simp [show src < 2^w by omega,show dst < 2^w by omega,show n < 2^w by omega]
      have hmc := ancestorRow_meetsContract (w := w) hp (ancestorJump parent k)
      obtain ⟨out,c,ret,hrun,hpost,_,hregs,hcost⟩ :=
        runs_call_of_meetsContract (r := 4) hmc hargs hwords
          ⟨src,dst,n,rfl,hw,hsrc,hd,Or.inl hs.le,
            fun v hv => ⟨ancestorJump_lt (fun i hi => (hparent i hi).1) k hv, hdone k le_rfl v hv⟩⟩ ω
      obtain ⟨_,hrow,hframe'⟩ := hpost
      change ∀ v < n, out.mem (dst+v) = ancestorJump parent k (ancestorJump parent k v) at hrow
      change ∀ a, a < dst ∨ dst+n ≤ a → out.mem a = st.mem a at hframe'
      refine ⟨.normal,out,c,hrun,⟨?_,(hregs 3 (by decide)).trans h3⟩,?_⟩
      · refine ⟨(hregs 0 (by decide)).trans h0,(hregs 1 (by decide)).trans h1,
          (hregs 2 (by decide)).trans h2,by simp,?_,?_⟩
        · intro j hj v hv
          by_cases heq : j = k+1
          · subst j
            exact (hrow v hv).trans (ancestorJump_succ parent k v).symm
          · have hj' : j ≤ k := by omega
            have hle := Nat.mul_le_mul_right n (show j+1 ≤ k+1 by omega)
            rw [Nat.succ_mul] at hle
            exact (hframe' _ (Or.inl (by dsimp [dst]; omega))).trans (hdone j hj' v hv)
        · intro a ha
          have hprev : base+(k+1)*n ≤ a ∨ a < base+n := by
            rw [Nat.succ_mul] at ha
            omega
          apply Eq.trans (hframe' a ?_) (hframe a (hprev.symm))
          rw [Nat.succ_mul] at ha
          have hdn : n ≤ (k+1)*n := Nat.le_mul_of_pos_left n (by omega)
          dsimp [dst]
          omega
      · change c ≤ argsSize ancestorTableArgs + (20*n+10) + 1 at hcost
        simp [ancestorTableArgs,argsSize,Expr.size] at hcost
        change c ≤ 20*n+31
        omega)
  refine loop.conseq (fun _ h => h) ?_ (by intro _ _; simp [Expr.size, Nat.mul_comm, Nat.add_assoc])
  intro o st h
  cases o with
  | normal => exact h.2.2.2.2
  | returned _ => exact h

end MinCostFlow.LastLevelProgram
