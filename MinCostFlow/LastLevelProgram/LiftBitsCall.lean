module

public import MinCostFlow.LastLevelProgram.LiftBits
import WordRAM.Tactic

/-!
# The depth-alignment pass on the ancestor table

Read one table row per binary digit. A zero digit leaves the
vertex in place, and a one digit replaces it by the stored jump.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

private theorem climbBits_last (parent : ℕ → ℕ) (i k : ℕ) (s : ℕ × ℕ) :
    climbBits parent (i+1) k s = climbBit parent (k+i) (climbBits parent i k s) := by
  induction i generalizing k s with
  | zero => rfl
  | succ i ih =>
    rw [climbBits, ih, Nat.add_right_comm, ← climbBits, Nat.add_assoc]

/-- One row lookup and one binary digit. -/
def climbBitBody : Stmt :=
  .assign 6 (.bin .mod (.reg 4) (.const 2)) ;;
  .assign 3 (.bin .add
    (.bin .mul (.bin .sub (.const 1) (.reg 6)) (.reg 3))
    (.bin .mul (.reg 6)
      (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.reg 5) (.reg 1))) (.reg 3))))) ;;
  .assign 4 (.bin .div (.reg 4) (.const 2))

/-- Input registers are `[table, vertices, row count, vertex, distance]`. -/
def climbBitsLoop : Stmt :=
  forRange 5 (.const 0) (.reg 2) climbBitBody

private theorem climbBit_runs {w : ℕ} (p : Program) (ω : ℕ → Bool)
    (st : State) (base n i v d jump : ℕ)
    (h0 : st.regs 0 = base) (h1 : st.regs 1 = n) (h3 : st.regs 3 = v)
    (h4 : st.regs 4 = d) (h5 : st.regs 5 = i)
    (hcell : st.mem (base+i*n+v) = jump)
    (hword : 2 < 2^w) (hav : base+i*n+v < 2^w)
    (hvw : v < 2^w) (hj : jump < 2^w) (hd : d < 2^w) :
    ∃ out c, Runs w p ω climbBitBody st .normal out c ∧ c ≤ 32 ∧
      out.mem = st.mem ∧ (∀ r, r ≠ 3 → r ≠ 4 → r ≠ 6 → out.regs r = st.regs r) ∧
      out.regs 3 = (if d % 2 = 0 then v else jump) ∧ out.regs 4 = d / 2 := by
  let b := d % 2
  let r := if d % 2 = 0 then v else jump
  have hb : b < 2 := Nat.mod_lt _ (by decide)
  have hb' : b < 2^w := hb.trans hword
  have hdiv : d/2 < 2^w := (Nat.div_le_self _ _).trans_lt hd
  have hadd : (1-b)*v + b*jump = r := by
    have he : b=0 ∨ b=1 := by omega
    rcases he with he | he
    · have he' : d%2=0 := he
      simp [r,he,he']
    · have he' : d%2=1 := he
      simp [r,he,he']
  have hv' : r < 2^w := by dsimp [r]; split <;> assumption
  have hleft : (1-b)*v < 2^w := by
    have he : b=0 ∨ b=1 := by omega
    rcases he with he | he <;> simp [he,hvw]
  have hright : b*jump < 2^w := by
    have he : b=0 ∨ b=1 := by omega
    rcases he with he | he <;> simp [he,hj]
  have hsum : (1-b)*v + b*jump < 2^w := hadd ▸ hv'
  have hiw : i*n < 2^w := by omega
  have hbase : base+i*n < 2^w := by omega
  let first := { st with regs := Function.update st.regs 6 b }
  let second := { first with regs := Function.update first.regs 3 r }
  let out := { second with regs := Function.update second.regs 4 (d/2) }
  have hfirst : Runs w p ω (.assign 6 (.bin .mod (.reg 4) (.const 2))) st .normal first 4 :=
    runs_assign_iff.mpr ⟨b,by eval_expr,rfl,rfl,rfl⟩
  have hsecond : Runs w p ω
      (.assign 3 (.bin .add
        (.bin .mul (.bin .sub (.const 1) (.reg 6)) (.reg 3))
        (.bin .mul (.reg 6)
          (.load (.bin .add (.bin .add (.reg 0) (.bin .mul (.reg 5) (.reg 1))) (.reg 3))))))
      first .normal second 17 := by
    have h60 : first.regs 6 = b := by simp [first]
    have h00 : first.regs 0 = base := h0
    have h11 : first.regs 1 = n := h1
    have h33 : first.regs 3 = v := h3
    have h55 : first.regs 5 = i := h5
    have hmem : first.mem (base+i*n+v) = jump := hcell
    have hsub : 1-b < 2^w := by omega
    refine runs_assign_iff.mpr ⟨r,?_,rfl,rfl,rfl⟩
    rw [← hadd]
    eval_expr
  have hfinal : Runs w p ω (.assign 4 (.bin .div (.reg 4) (.const 2))) second .normal out 4 := by
    have h44 : second.regs 4 = d := h4
    exact runs_assign_iff.mpr ⟨d/2,by eval_expr,rfl,rfl,rfl⟩
  refine ⟨out,27,?_ ,by decide,rfl,?_,?_,?_⟩
  · unfold climbBitBody
    exact runs_seq_iff.mpr (Or.inr ⟨first,4,22,hfirst,
      runs_seq_iff.mpr (Or.inr ⟨second,17,4,hsecond,hfinal,rfl⟩),rfl⟩)
  · intro x hx₁ hx₂ hx₃
    simp [out,second,first,Function.update_of_ne hx₁,Function.update_of_ne hx₂,Function.update_of_ne hx₃]
  · simp [out,second,r]
  · simp [out]

/-- Read the low bits in logarithmically many table lookups. -/
theorem climbBitsLoop_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (base n count v d other : ℕ) (parent : ℕ → ℕ)
    (hword : 2 < 2^w) (hcount : count < 2^w) (hv : v < n) (hd : d < 2^w)
    (hroom : base+count*n < 2^w)
    (hparent : ∀ x < n, parent x < n)
    (htable : ∀ i < count, ∀ x < n, mem (base+i*n+x) = ancestorJump parent i x) :
    Triple w p (fun st => st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 = count ∧
        st.regs 3 = v ∧ st.regs 4 = d ∧ st.regs 9 = other ∧ st.mem = mem) climbBitsLoop
      (normalPost fun st => st.mem = mem ∧ st.regs 0 = base ∧ st.regs 1 = n ∧
        st.regs 2 = count ∧ st.regs 9 = other ∧ st.regs 3 < n ∧
        st.regs 3 = (climbBits parent count 0 (v,d)).1)
      (fun _ => 41*count+7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 = count ∧ st.regs 5 = i ∧
    (st.regs 3,st.regs 4) = climbBits parent i 0 (v,d) ∧
    st.regs 3 < n ∧ st.regs 4 < 2^w ∧ st.mem = mem ∧ st.regs 9 = other
  have loop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (body := climbBitBody) (Inv := Inv)
    (P := fun st => st.regs 0 = base ∧ st.regs 1 = n ∧ st.regs 2 = count ∧
      st.regs 3 = v ∧ st.regs 4 = d ∧ st.regs 9 = other ∧ st.mem = mem)
    32 0 count (Nat.zero_le _) (by omega) (fun _ => hcount)
    (fun st ⟨h0,h1,h2,h3,h4,h9,hm⟩ => by
      exact ⟨by eval_expr, by simp [Inv,climbBits,h0,h1,h2,h3,h4,h9,hm,hv,hd]⟩)
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ st _ _ h => by
      have hr : st.regs 2 = count := h.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h5,hmodel,hu,hr,hm,h9⟩
      let x := st.regs 3
      let r := st.regs 4
      let y := ancestorJump parent i x
      have hy : y < n := ancestorJump_lt hparent i hu
      have hle := Nat.mul_le_mul_right n (show i+1 ≤ count by omega)
      rw [Nat.succ_mul] at hle
      have ha : base+i*n+x < 2^w := by dsimp [x]; omega
      have hxw : x < 2^w := by dsimp [x]; omega
      have hyw : y < 2^w := by omega
      have hat : st.mem (base+i*n+x) = y := by rw [hm]; exact htable i hi x hu
      obtain ⟨out,c,hc,hcost,hmem,hregs,hx,hr'⟩ :=
        climbBit_runs p ω st base n i x r y h0 h1 rfl rfl h5 hat hword ha hxw hyw hr
      have hmodel' : (out.regs 3,out.regs 4) = climbBits parent (i+1) 0 (v,d) := by
        rw [climbBits_last, Nat.zero_add, ← hmodel]
        exact Prod.ext hx hr'
      refine ⟨.normal,out,c,hc,⟨?_,(hregs 5 (by decide) (by decide) (by decide)).trans h5⟩,hcost⟩
      refine ⟨(hregs 0 (by decide) (by decide) (by decide)).trans h0,
        (hregs 1 (by decide) (by decide) (by decide)).trans h1,
        (hregs 2 (by decide) (by decide) (by decide)).trans h2,by simp,hmodel',?_,?_,hmem.trans hm,?_⟩
      · change Function.update out.regs 5 (i+1) 3 < n
        rw [Function.update_of_ne (by decide : (3 : ℕ) ≠ 5), hx]
        split <;> assumption
      · change Function.update out.regs 5 (i+1) 4 < 2^w
        rw [Function.update_of_ne (by decide : (4 : ℕ) ≠ 5), hr']
        exact (Nat.div_le_self _ _).trans_lt hr
      · change Function.update out.regs 5 (i+1) 9 = other
        rw [Function.update_of_ne (by decide : (9 : ℕ) ≠ 5)]
        exact (hregs 9 (by decide) (by decide) (by decide)).trans h9)
  refine loop.conseq (fun _ h => h) ?_ (by intro _ _; simp [Expr.size,Nat.mul_comm])
  intro o st h
  cases o with
  | returned _ => exact h
  | normal =>
    obtain ⟨h0,h1,h2,_,hmodel,hu,_,hm,h9⟩ := h
    exact ⟨hm,h0,h1,h2,h9,hu,congrArg Prod.fst hmodel⟩

end MinCostFlow.LastLevelProgram
