module

public import MinCostFlow.LastLevelProgram.FormatBit
public import MinCostFlow.LastLevelProgram.QueryFormat
import Mathlib.Data.Nat.Size
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic
import WordRAM.Tactic

/-!
# Bit width of a caller length block

For the canonical graph query in Definition 5.8 (pages 19–20),
the highest nonzero solver limb determines the unsigned width.
The program can obtain its bit count with four word comparisons.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- The bit count in a four-bit solver limb is the number of binary
thresholds it reaches. -/
def solverLimbSizeExpr : Expr :=
  .bin .add
    (.bin .add (.bin .lt (.const 0) (.reg 0)) (.bin .lt (.const 1) (.reg 0)))
    (.bin .add (.bin .lt (.const 3) (.reg 0)) (.bin .lt (.const 7) (.reg 0)))

/-- Return the bit count of one solver limb. -/
def solverLimbSizeBody : Stmt := .ret solverLimbSizeExpr

/-- Reading a limb's bit count takes constant time and leaves memory unchanged. -/
theorem solverLimbSize_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos x : ℕ) (hw : 16 ≤ 2^w) (hx : x < 16) :
    ∃ o out cost, Runs w p ω solverLimbSizeBody (startState [x] mem pos) o out cost ∧
      (o.value = x.size ∧ out.mem = mem) ∧ cost ≤ 16 := by
  have he : Expr.eval w (startState [x] mem pos) solverLimbSizeExpr = some x.size := by
    interval_cases x <;> simp [solverLimbSizeExpr,Expr.eval,BinOp.eval,startState,
      Option.getD_some,
      show 0 < 2^w by omega,show 1 < 2^w by omega,show 2 < 2^w by omega,
      show 3 < 2^w by omega,show 4 < 2^w by omega,show 7 < 2^w by omega]
    all_goals decide +kernel
  apply runs_start_le
  unfold solverLimbSizeBody
  exact runs_ret_le he ⟨rfl,rfl⟩ (by decide)

/-- A positive high part determines the bit count after prepending a
valid low limb. A zero high part leaves only the low limb. -/
theorem size_prependSolverLimb {low high : ℕ} (hl : low < 16) :
    (low+16*high).size = if high = 0 then low.size else 4+high.size := by
  by_cases hh : high = 0
  · simp [hh]
  rw [ite_eq_right hh]
  have hb : 0 < high.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero hh)
  have hhi := Nat.lt_size_self high
  have hlo : (2:ℕ)^(high.size-1) ≤ high := Nat.lt_size.mp (by omega)
  apply le_antisymm
  · apply Nat.size_le.mpr
    rw [pow_add]
    change low+16*high < 16*2^high.size
    omega
  · have h : 4+high.size-1 < (low+16*high).size := by
      apply Nat.lt_size.mpr
      rw [show 4+high.size-1 = 4+(high.size-1) by omega,pow_add]
      change 16*2^(high.size-1) ≤ low+16*high
      omega
    omega

/-- Read-only interface for the size of a solver limb. -/
def solverLimbSizeContract (w : ℕ) : Contract where
  pre args _ := ∃ x, args = [x] ∧ 16 ≤ 2^w ∧ x < 16
  post args mem ret out := ret = (args.getD 0 0).size ∧ out = mem
  cost _ _ := 16

/-- The installed limb size procedure meets its read-only interface. -/
theorem solverLimbSize_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.procs[entry]? = some solverLimbSizeBody) :
    MeetsContract w p entry (solverLimbSizeContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨x,rfl,hw,hx⟩ := hpre
  exact solverLimbSize_runs (p := p) (ω := ω) mem pos x hw hx

/-- Extend the width of the scanned high part by one low limb. -/
def blockWidthStepBody (limb : ℕ) : Stmt :=
  .cond (.reg 1) (.ret (.bin .add (.const 4) (.reg 1)))
    (.seq (.call 2 limb [.reg 0]) (.ret (.reg 2)))

/-- The scan step extends the width in constant time and preserves memory. -/
theorem blockWidthStep_runs {w limb : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp : MeetsContract w p limb (solverLimbSizeContract w))
    (mem : ℕ → ℕ) (pos low high : ℕ) (hw : 16 ≤ 2^w) (hl : low < 16)
    (hh : 4+high.size < 2^w) :
    ∃ o out cost, Runs w p ω (blockWidthStepBody limb)
      (startState [low,high.size] mem pos) o out cost ∧
      (o.value = (low+16*high).size ∧ out.mem = mem) ∧ cost ≤ 24 := by
  let st := startState [low,high.size] mem pos
  have hreg : Expr.eval w st (.reg 1) = some high.size := rfl
  rw [size_prependSolverLimb hl]
  by_cases hz : high = 0
  · have hs : high.size = 0 := Nat.size_eq_zero.mpr hz
    rw [ite_eq_left hz]
    have hcall : ∃ o out cost, Runs w p ω
          (.seq (.call 2 limb [.reg 0]) (.ret (.reg 2))) st o out cost ∧
        (o.value = low.size ∧ out.mem = mem) ∧ cost ≤ 21 := by
      apply runs_start_le
      refine runs_seq_call_le hp (vs := [low]) rfl ?_ ⟨low,rfl,hw,hl⟩ ?_
      · intro x hx
        obtain rfl : x = low := by simpa using hx
        omega
      · intro ret mid next hpost
        obtain ⟨hret,hmem⟩ := hpost
        change ret = low.size at hret
        refine runs_ret_le (v := ret) (by eval_expr) ⟨hret,hmem⟩ ?_
        change 0+1+16+2+2 ≤ 21
        decide
    obtain ⟨o,out,c,hr,hpost,hc⟩ := hcall
    refine ⟨o,out,1+c+1,?_,hpost,by omega⟩
    exact runs_cond_iff.mpr ⟨0,c,hs ▸ hreg,by simpa using hr,rfl⟩
  · have hs : high.size ≠ 0 := fun h => hz (Nat.size_eq_zero.mp h)
    rw [ite_eq_right hz]
    have he : Expr.eval w st (.bin .add (.const 4) (.reg 1)) = some (4+high.size) := by
      dsimp [st]
      eval_expr
    have hr : Runs w p ω (.ret (.bin .add (.const 4) (.reg 1))) st
        (.returned (4+high.size)) st 4 :=
      runs_ret_iff.mpr ⟨_,he,rfl,rfl,rfl⟩
    refine ⟨.returned (4+high.size),st,6,?_,⟨rfl,rfl⟩,by decide⟩
    exact runs_cond_iff.mpr ⟨high.size,4,hreg,by simpa [hs] using hr,rfl⟩

/-- The scan step needs only the size of the high part. -/
def blockWidthStepContract (w : ℕ) : Contract where
  pre args _ := ∃ low count, args = [low,count] ∧ 16 ≤ 2^w ∧ low < 16 ∧ 4+count < 2^w
  post args mem ret out :=
    ret = (if args.getD 1 0 = 0 then (args.getD 0 0).size else 4+args.getD 1 0) ∧ out = mem
  cost _ _ := 24

/-- Link the block width step using its word-sized count argument. -/
theorem blockWidthStep_meetsContract {w entry limb : ℕ} {p : Program}
    (he : p.procs[entry]? = some (blockWidthStepBody limb))
    (hp : MeetsContract w p limb (solverLimbSizeContract w)) :
    MeetsContract w p entry (blockWidthStepContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨low,count,rfl,hw,hl,hc⟩ := hpre
  let high := if count = 0 then 0 else 2^(count-1)
  have hs : high.size = count := by
    by_cases h : count = 0
    · simp [high,h]
    · simp [high,h,Nat.size_pow,show count-1+1 = count by omega]
  have hz : high = 0 ↔ count = 0 := by rw [← hs,Nat.size_eq_zero]
  obtain ⟨o,out,c,hrun,⟨hvalue,hmem⟩,hcost⟩ :=
    blockWidthStep_runs (ω := ω) hp mem pos low high hw hl (hs.symm ▸ hc)
  simp only [size_prependSolverLimb hl,hs,hz] at hvalue
  exact ⟨o,out,c,hs ▸ hrun,⟨hvalue,hmem⟩,hcost⟩

/-- Scan the block from the high end. The two inputs are the block base
and its caller limb count. -/
def blockWidthLoop (entry : ℕ) : Stmt :=
  forRange 3 (.const 0) (.reg 1)
    (.call 2 entry [.load (.bin .add (.reg 0) (.bin .sub (.reg 1)
      (.bin .add (.reg 3) (.const 1)))), .reg 2])

/-- The scan returns the exact bit count and preserves memory in linear
time in the caller limb count. -/
theorem blockWidthLoop_triple {w entry : ℕ} {p : Program}
    (hp : MeetsContract w p entry (blockWidthStepContract w))
    (mem : ℕ → ℕ) (pos a L : ℕ) (hw : 16 ≤ 2^w)
    (ha : a+L < 2^w) (hL : 4*L < 2^w) (hv : Num.Valid mem a 4 L) :
    Triple w p (fun st => st = startState [a,L] mem pos) (blockWidthLoop entry)
      (normalPost fun st => st.mem = mem ∧ st.regs 2 = (Num.unsignedVal mem a 4 L).size)
      (fun _ => 43*L+7) := by
  let args : List Expr := [.load (.bin .add (.reg 0) (.bin .sub (.reg 1)
    (.bin .add (.reg 3) (.const 1)))), .reg 2]
  let Inv := fun i (st : State) => st.regs 0 = a ∧ st.regs 1 = L ∧ st.regs 3 = i ∧
    st.mem = mem ∧ st.regs 2 = (Num.unsignedVal mem (a+(L-i)) 4 i).size
  have loop := Triple.forRange_const (w := w) (p := p) (r := 3)
    (lo := .const 0) (hi := .reg 1) (body := .call 2 entry args) (Inv := Inv)
    (P := fun st => st = startState [a,L] mem pos)
    34 0 L (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st he => by subst st; exact ⟨by eval_expr, by simp [Inv,startState,Num.unsignedVal]⟩)
    (fun _ _ _ _ h => h.2.2.1)
    (fun _ st _ _ h => by have hreg := h.2.1; eval_expr)
    (fun i _ hi st ω ⟨h0,h1,h3,hm,h2⟩ => by
      let offset := L-(i+1)
      let x := mem (a+offset)
      let high := Num.unsignedVal mem (a+(L-i)) 4 i
      have ho : offset < L := by dsimp [offset]; omega
      have hx : x < 16 := hv offset ho
      have hv' : Num.Valid mem (a+(L-i)) 4 i := by
        intro j hj
        simpa [Nat.add_assoc] using hv (L-i+j) (by omega)
      have hu := Num.unsignedVal_lt hv'
      rw [Num.capacity_eq_two_pow] at hu
      have hsize : high.size ≤ 4*i := Nat.size_le.mpr hu
      have hfit : 4+high.size < 2^w := by omega
      have hidx : i+1 < 2^w := by omega
      have haddress : a+offset < 2^w := by omega
      have hoff : offset < 2^w := by omega
      have hmAt : Expr.MemAt st (a+offset) x := congrFun hm _
      have heval : evalArgs w st args = some [x,high.size] := by
        dsimp [args,offset,x,high] at *
        eval_expr
      obtain ⟨out,cost,ret,hr,hpost,hret,hframe,hcost⟩ :=
        runs_call_of_meetsContract (r := 2) hp heval
          (by intro word hw'; simp at hw'; rcases hw' with rfl | rfl <;> omega)
          ⟨x,high.size,rfl,hw,hx,hfit⟩ ω
      obtain ⟨hval,hmem⟩ := hpost
      have hbase : a+offset+1 = a+(L-i) := by dsimp [offset]; omega
      refine ⟨.normal,out,cost,hr,⟨⟨(hframe 0 (by decide)).trans h0,
        (hframe 1 (by decide)).trans h1,by simp,hmem.trans hm,?_⟩,
        (hframe 3 (by decide)).trans h3⟩,?_⟩
      · change Function.update out.regs 3 (i+1) 2 = _
        rw [Function.update_of_ne (by decide : 2 ≠ 3),hret,hval]
        change (if high.size = 0 then x.size else 4+high.size) =
          (Num.unsignedVal mem (a+offset) 4 (i+1)).size
        rw [Num.unsignedVal,hbase]
        change _ = (x+16*high).size
        simp only [size_prependSolverLimb hx,Nat.size_eq_zero]
      · apply hcost.trans
        change 9+24+1 ≤ 34
        decide)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal => exact ⟨h.2.2.2.1, by simpa using h.2.2.2.2⟩
  · intro st _
    simp only [Nat.sub_zero,Expr.size]
    rw [Nat.mul_comm L]

/-- Run the high-to-low scan and return the accumulator. -/
def blockWidthBody (step : ℕ) : Stmt :=
  .seq (blockWidthLoop step) (.ret (.reg 2))

/-- The scan returns the unsigned source bit width without writing memory. -/
def blockWidthContract (w : ℕ) : Contract where
  pre args mem := ∃ a L, args = [a,L] ∧ 16 ≤ 2^w ∧ a+L < 2^w ∧
    4*L < 2^w ∧ Num.Valid mem a 4 L
  post args mem ret out := ∃ a L, args = [a,L] ∧
    ret = (Num.unsignedVal mem a 4 L).size ∧ out = mem
  cost args _ := 43*args.getD 1 0+10

/-- Install the block-width scan with its linear cost. -/
theorem blockWidth_meetsContract {w entry step : ℕ} {p : Program}
    (he : p.procs[entry]? = some (blockWidthBody step))
    (hp : MeetsContract w p step (blockWidthStepContract w)) :
    MeetsContract w p entry (blockWidthContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨a,L,rfl,hw,ha,hL,hv⟩ := hpre
  apply runs_start_le
  unfold blockWidthBody
  refine runs_seq_triple_le (blockWidthLoop_triple hp mem pos a L hw ha hL hv) rfl ?_
  intro out ⟨hm,hr⟩
  refine runs_ret_le (v := (Num.unsignedVal mem a 4 L).size) (by eval_expr)
    ⟨a,L,rfl,rfl,hm⟩ ?_
  change 0+(43*L+7)+1+2 ≤ 43*L+10
  omega

/-- Read a block width and raise the running maximum at the guest
precision. The arguments are `[base, L, P, Q, previous]`. -/
def raiseGuestWidthBody (block : ℕ) : Stmt :=
  .seq (.call 5 block [.reg 0,.reg 1])
    (.seq (.assign 6 (.bin .sub (.bin .add (.reg 5) (.reg 3)) (.reg 2)))
      (.ret (.bin .add (.reg 4) (.bin .sub (.reg 6) (.reg 4)))))

/-- One positive solver length raises the maximum to its canonical
guest numerator bit count if that count is larger. -/
theorem raiseGuestWidth_runs {w block : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp : MeetsContract w p block (blockWidthContract w))
    (mem : ℕ → ℕ) (pos a L P Q previous : ℕ)
    (hw : 16 ≤ 2^w) (ha : a+L < 2^w) (hL : 4*L+Q < 2^w)
    (_hP : P < 2^w) (_hprev : previous < 2^w)
    (hv : Num.Valid mem a 4 L) (hpos : 0 < Num.intVal mem a 4 L) :
    ∃ o out cost, Runs w p ω (raiseGuestWidthBody block)
      (startState [a,L,P,Q,previous] mem pos) o out cost ∧
      (o.value = max previous (queryNumerator Q (Num.fixVal mem a 4 L P)).natAbs.size ∧
        out.mem = mem) ∧ cost ≤ 43*L+28 := by
  apply runs_start_le
  unfold raiseGuestWidthBody
  refine runs_seq_call_le hp (vs := [a,L]) rfl ?_ ⟨a,L,rfl,hw,ha,by omega,hv⟩ ?_
  · intro x hx
    rcases (show x = a ∨ x = L by simpa using hx) with rfl | rfl <;> omega
  · intro ret mid pos' hpost
    obtain ⟨b,N,he,hret,hmem⟩ := hpost
    simp only [List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl⟩ := he
    have hsize : ret ≤ 4*L := by
      rw [hret]
      apply Nat.size_le.mpr
      change Num.unsignedVal mem a 4 L < 2^(4*L)
      simpa only [Num.capacity_eq_two_pow] using Num.unsignedVal_lt hv
    have hQ : Q < 2^w := by omega
    have hsum : ret+Q < 2^w := by omega
    have hdiff : ret+Q-P < 2^w := by omega
    refine runs_seq_assign_le (v := ret+Q-P) (by eval_expr) ?_
    have hdiff' : ret+Q-P-previous < 2^w := by omega
    have hmax : previous+(ret+Q-P-previous) = max previous (ret+Q-P) := by omega
    have hmaxFit : previous+(ret+Q-P-previous) < 2^w := by omega
    refine runs_ret_le (v := previous+(ret+Q-P-previous)) (by eval_expr) ⟨?_,hmem⟩ ?_
    · rw [Outcome.value,hmax,queryNumerator_size_of_positiveBlock hv hpos,hret]
      rfl
    · change 0+2+(43*L+10)+2+5+2+6 ≤ 43*L+28
      omega

/-- The per-edge width scan raises a word-sized maximum. -/
def raiseGuestWidthContract (w : ℕ) : Contract where
  pre args mem := ∃ a L P Q prev, args = [a,L,P,Q,prev] ∧
    16 ≤ 2^w ∧ a+L < 2^w ∧ 4*L+Q < 2^w ∧
    Num.Valid mem a 4 L ∧ 0 < Num.intVal mem a 4 L
  post args mem ret out := ∃ a L P Q prev, args = [a,L,P,Q,prev] ∧
    ret = max prev (queryNumerator Q (Num.fixVal mem a 4 L P)).natAbs.size ∧ out = mem
  cost args _ := 43*args.getD 1 0+28

/-- Install the per-edge width scan. -/
theorem raiseGuestWidth_meetsContract {w entry block : ℕ} {p : Program}
    (he : p.procs[entry]? = some (raiseGuestWidthBody block))
    (hp : MeetsContract w p block (blockWidthContract w)) :
    MeetsContract w p entry (raiseGuestWidthContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨a,L,P,Q,prev,rfl,hw,ha,hL,hv,hpos⟩ := hpre
  obtain ⟨o,out,c,hrun,hpost,hcost⟩ :=
    raiseGuestWidth_runs (ω := ω) hp mem pos a L P Q prev hw ha hL
      (hwords _ (by simp)) (hwords _ (by simp)) hv hpos
  exact ⟨o,out,c,hrun,⟨a,L,P,Q,prev,rfl,hpost⟩,hcost⟩

/-- Scan live edge names and keep the greatest guest bit count. The
initial maximum in register five is the weight-bound bit count. -/
def guestWidthArgs : List Expr :=
  [.bin .add (.reg 1) (.bin .mul (.load (.bin .add (.reg 0) (.reg 7))) (.reg 2)),
    .reg 2,.reg 3,.reg 4,.reg 5]

/-- Visit each live solver length once. -/
def guestWidthLoop (entry : ℕ) : Stmt :=
  forRange 7 (.const 0) (.reg 6) (.call 5 entry guestWidthArgs)

/-- The maximum-width scan reads only the named lengths and costs at
most one linear block scan per edge. -/
theorem guestWidthLoop_triple {w entry : ℕ} {p : Program}
    (hp : MeetsContract w p entry (raiseGuestWidthContract w))
    (mem : ℕ → ℕ) (pos names lengths L P Q initial m : ℕ) (name : ℕ → ℕ)
    (hw : 16 ≤ 2^w) (hL : 4*L+Q < 2^w) (hP : P < 2^w)
    (hiFit : initial < 2^w) (hm : names+m < 2^w)
    (hblocks : ∀ i < m, mem (names+i) = name i ∧ lengths+name i*L+L < 2^w ∧
      Num.Valid mem (lengths+name i*L) 4 L ∧ 0 < Num.intVal mem (lengths+name i*L) 4 L) :
    let count := fun i => (queryNumerator Q
      (Num.fixVal mem (lengths+name i*L) 4 L P)).natAbs.size
    Triple w p (fun st => st = startState [names,lengths,L,P,Q,initial,m] mem pos)
      (guestWidthLoop entry)
      (normalPost fun st => st.mem = mem ∧
        st.regs 5 = max initial ((Finset.range m).sup count))
      (fun _ => (43*L+50)*m+7) := by
  intro count
  let Inv := fun i (st : State) =>
    st.regs 0 = names ∧ st.regs 1 = lengths ∧ st.regs 2 = L ∧ st.regs 3 = P ∧
    st.regs 4 = Q ∧ st.regs 6 = m ∧ st.regs 7 = i ∧ st.mem = mem ∧
    st.regs 5 = max initial ((Finset.range i).sup count) ∧ st.regs 5 < 2^w
  have loop := Triple.forRange_const (w := w) (p := p) (r := 7) (lo := .const 0)
    (hi := .reg 6) (body := .call 5 entry guestWidthArgs) (Inv := Inv)
    (P := fun st => st = startState [names,lengths,L,P,Q,initial,m] mem pos)
    (43*L+41) 0 m (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st he => by subst st; exact ⟨by eval_expr, by simp [Inv,startState,hiFit]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by have hr := h.2.2.2.2.2.1; eval_expr)
    (fun i _ hi st ω ⟨h0,h1,h2,h3,h4,h6,h7,hmem,h5,hprev⟩ => by
      obtain ⟨hn,ha,hv,hpos⟩ := hblocks i hi
      let a := lengths+name i*L
      let prev := st.regs 5
      have hmAt : Expr.MemAt st (names+i) (name i) := (congrFun hmem _).trans hn
      have haWord : a < 2^w := by dsimp [a]; omega
      have hargs : evalArgs w st guestWidthArgs = some [a,L,P,Q,prev] := by
        have haddr : names+i < 2^w := by omega
        have hprod : name i*L < 2^w := by omega
        dsimp [guestWidthArgs,a,prev]
        eval_expr
      obtain ⟨out,cost,ret,hr,hpost,hret,hframe,hcost⟩ :=
        runs_call_of_meetsContract (r := 5) hp hargs
          (by
            intro x hx
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega)
          ⟨a,L,P,Q,prev,rfl,hw,ha,hL,hmem.symm ▸ hv,hmem.symm ▸ hpos⟩ ω
      obtain ⟨b,N,R,S,old,he,hvalue,hout⟩ := hpost
      simp only [List.cons.injEq,and_true] at he
      obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
      have hval : ret = max prev (count i) := by simpa only [count,a,hmem] using hvalue
      have hcount : count i < 2^w := by
        change (queryNumerator Q (Num.fixVal mem a 4 L P)).natAbs.size < 2^w
        rw [queryNumerator_size_of_positiveBlock hv hpos]
        have hs : (Num.unsignedVal mem a 4 L).size ≤ 4*L := Nat.size_le.mpr
          (by simpa only [Num.capacity_eq_two_pow] using Num.unsignedVal_lt hv)
        dsimp [a] at hs
        omega
      have hnext : out.regs 5 = max initial ((Finset.range (i+1)).sup count) := by
        rw [hret,hval,show prev = _ from h5,Finset.range_add_one,Finset.sup_insert]
        ac_rfl
      refine ⟨.normal,out,cost,hr,⟨⟨(hframe 0 (by decide)).trans h0,
        (hframe 1 (by decide)).trans h1,(hframe 2 (by decide)).trans h2,
        (hframe 3 (by decide)).trans h3,(hframe 4 (by decide)).trans h4,
        (hframe 6 (by decide)).trans h6,by simp,hout.trans hmem,?_,?_⟩,
        (hframe 7 (by decide)).trans h7⟩,?_⟩
      · simpa using hnext
      · have hb : ret < 2^w := by rw [hval]; exact max_lt hprev hcount
        simpa [hret] using hb
      · apply hcost.trans
        change 12+(43*L+28)+1 ≤ 43*L+41
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st hs
    cases o with
    | returned => exact hs
    | normal => exact ⟨hs.2.2.2.2.2.2.2.1, hs.2.2.2.2.2.2.2.2.1⟩
  · intro st _
    simp only [Nat.sub_zero,Expr.size]
    rw [Nat.mul_comm m]

/-- Return the maximum width plus one sign bit. -/
def guestWidthBody (raise : ℕ) : Stmt :=
  .seq (guestWidthLoop raise) (.ret (.bin .add (.reg 5) (.const 1)))

/-- The installed scan returns the signed guest limb count. -/
def guestWidthContract (w names lengths L P Q initial m : ℕ) (name : ℕ → ℕ) : Contract where
  pre args mem := args = [names,lengths,L,P,Q,initial,m] ∧
    16 ≤ 2^w ∧ 4*L+Q+1 < 2^w ∧ P < 2^w ∧ initial+1 < 2^w ∧ names+m < 2^w ∧
    ∀ i < m, mem (names+i) = name i ∧ lengths+name i*L+L < 2^w ∧
      Num.Valid mem (lengths+name i*L) 4 L ∧ 0 < Num.intVal mem (lengths+name i*L) 4 L
  post _ mem ret out := out = mem ∧
    ret = max initial ((Finset.range m).sup fun i =>
      (queryNumerator Q (Num.fixVal mem (lengths+name i*L) 4 L P)).natAbs.size)+1
  cost _ _ := (43*L+50)*m+12

/-- The callable width scan includes the sign-bit addition in its cost. -/
theorem guestWidth_meetsContract {w entry raise names lengths L P Q initial m : ℕ}
    {p : Program} (name : ℕ → ℕ)
    (he : p.procs[entry]? = some (guestWidthBody raise))
    (hp : MeetsContract w p raise (raiseGuestWidthContract w)) :
    MeetsContract w p entry (guestWidthContract w names lengths L P Q initial m name) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨rfl,hw,hL,hP,hinit,hm,hblocks⟩ := hpre
  apply runs_start_le
  unfold guestWidthBody
  refine runs_seq_triple_le
    (guestWidthLoop_triple hp mem pos names lengths L P Q initial m name hw
      (by omega) hP (by omega) hm hblocks) rfl ?_
  intro st ⟨hm',hreg⟩
  have hbound : ((Finset.range m).sup fun i =>
      (queryNumerator Q (Num.fixVal mem (lengths+name i*L) 4 L P)).natAbs.size) ≤
      4*L+Q := by
    apply Finset.sup_le_iff.mpr
    intro i hi
    obtain ⟨_,_,hv,hpos⟩ := hblocks i (Finset.mem_range.mp hi)
    rw [queryNumerator_size_of_positiveBlock hv hpos]
    have hs : (Num.unsignedVal mem (lengths+name i*L) 4 L).size ≤ 4*L :=
      Nat.size_le.mpr (by simpa only [Num.capacity_eq_two_pow] using Num.unsignedVal_lt hv)
    omega
  have hfit : st.regs 5+1 < 2^w := by rw [hreg]; omega
  refine runs_ret_le (v := st.regs 5+1) (by eval_expr) ⟨hm',?_⟩ ?_
  · exact congrArg (·+1) hreg
  · change 0+((43*L+50)*m+7)+1+4 ≤ (43*L+50)*m+12
    omega

/-- A compact scan of all live edges returns the model's guest width
when its initial maximum is the weight-bound bit count. -/
theorem graphQueryLimbs_of_widthScan {G : MGraph} {Q B m : ℕ}
    (len : ℕ → ℝ) (name : ℕ → ℕ)
    (hn : ∀ e, e ∈ G.E ↔ ∃ i < m, name i = e) :
    graphQueryLimbs G Q B len = max B.size ((Finset.range m).sup fun i =>
      (queryNumerator Q (len (name i))).natAbs.size)+1 := by
  rw [graphQueryLimbs_eq_maxSize]
  have hs : (G.E.sup fun e => (queryNumerator Q (len e)).natAbs.size) =
      (Finset.range m).sup (fun i => (queryNumerator Q (len (name i))).natAbs.size) := by
    apply le_antisymm <;> apply Finset.sup_le_iff.mpr
    · intro e he
      obtain ⟨i,hi,rfl⟩ := (hn e).1 he
      exact Finset.le_sup (f := fun i => (queryNumerator Q (len (name i))).natAbs.size)
        (Finset.mem_range.mpr hi)
    · intro i hi
      exact Finset.le_sup (f := fun e => (queryNumerator Q (len e)).natAbs.size)
        ((hn _).2 ⟨i,Finset.mem_range.mp hi,rfl⟩)
  rw [hs]

end MinCostFlow.LastLevelProgram
