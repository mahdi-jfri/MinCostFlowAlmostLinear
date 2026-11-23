module

public import MinCostFlow.LastLevelProgram.QueryFormat
public import WordRAM.Logic
import Mathlib.Data.Nat.PadicValNat
import Mathlib.Tactic
import MinCostFlow.Num.DivisionSigns
import WordRAM.Tactic

/-!
# Binary valuation of a solver limb

The graph-derived LSST format for Definition 5.8 (pages 19–20) removes
common low zero bits from the length numerators. A four-bit solver
limb contributes the number of its low zero bits, with four for zero.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- The number of low zero bits in a four-bit limb, capped at four. -/
def limbValuation (x : ℕ) : ℕ :=
  if x = 0 then 4 else padicValNat 2 x

/-- Test whether register zero is divisible by a constant. -/
def zeroResidue (d : ℕ) : Expr :=
  .bin .eq (.bin .mod (.reg 0) (.const d)) (.const 0)

/-- The count is the sum of the tests for divisibility by two, four,
eight, and sixteen. For a four-bit limb the last test is equality to zero. -/
def limbValuationExpr : Expr :=
  .bin .add (.bin .add (zeroResidue 2) (zeroResidue 4))
    (.bin .add (zeroResidue 8) (.bin .eq (.reg 0) (.const 0)))

/-- Return the low zero bit count in one solver limb. -/
def limbValuationBody : Stmt := .ret limbValuationExpr

private theorem limbValuation_eval {w : ℕ} (mem : ℕ → ℕ) (pos x : ℕ)
    (hw : 16 ≤ 2^w) (hx : x < 16) :
    Expr.eval w (startState [x] mem pos) limbValuationExpr = some (limbValuation x) := by
  interval_cases x <;> simp (disch := omega) [limbValuationExpr, zeroResidue, Expr.eval, BinOp.eval,
    startState, limbValuation, List.getElem?_cons_zero, Option.getD_some,
    show 8 < 2^w by omega, show 4 < 2^w by omega, show 2 < 2^w by omega,
    show 1 < 2^w by omega, show 0 < 2^w by omega,
    show 3 < 2^w by omega, show 5 < 2^w by omega, show 6 < 2^w by omega,
    show 7 < 2^w by omega, Nat.reduceMod]
  all_goals decide +kernel

/-- Reading the valuation needs no writes and costs a constant number of steps. -/
theorem limbValuation_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos x : ℕ) (hw : 16 ≤ 2^w) (hx : x < 16) :
    ∃ o out cost, Runs w p ω limbValuationBody (startState [x] mem pos) o out cost ∧
      (o.value = limbValuation x ∧ out.mem = mem) ∧ cost ≤ 24 := by
  apply runs_start_le
  unfold limbValuationBody
  exact runs_ret_le (limbValuation_eval mem pos x hw hx) ⟨rfl,rfl⟩ (by decide)

/-- Callable interface for the low-zero-bit count of one solver limb. -/
def limbValuationContract (w : ℕ) : Contract where
  pre args _ := ∃ x, args = [x] ∧ 16 ≤ 2^w ∧ x < 16
  post args mem ret out := ret = limbValuation (args.getD 0 0) ∧ out = mem
  cost _ _ := 24

/-- The linked limb routine is read-only. -/
theorem limbValuation_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.procs[entry]? = some limbValuationBody) :
    MeetsContract w p entry (limbValuationContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω _ hpre
  obtain ⟨x,rfl,hw,hx⟩ := hpre
  exact limbValuation_runs (p := p) (ω := ω) mem pos x hw hx

/-- Prepending a low limb adds four if that limb is zero and otherwise
replaces the accumulated count by its own binary valuation. -/
def blockValuationStep (low highCount : ℕ) : ℕ :=
  limbValuation low + (if low = 0 then highCount else 0)

/-- Update the accumulated count when visiting a limb from high to low. -/
def blockValuationStepBody (limb : ℕ) : Stmt :=
  .seq (.call 2 limb [.reg 0])
    (.ret (.bin .add (.reg 2) (.bin .mul (.bin .eq (.reg 0) (.const 0)) (.reg 1))))

/-- Each block scan step reads only its input words and leaves memory unchanged. -/
theorem blockValuationStep_runs {w limb : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp : MeetsContract w p limb (limbValuationContract w))
    (mem : ℕ → ℕ) (pos low highCount : ℕ) (hw : 16 ≤ 2^w) (hx : low < 16)
    (hcount : highCount+4 < 2^w) :
    ∃ o out cost, Runs w p ω (blockValuationStepBody limb)
      (startState [low,highCount] mem pos) o out cost ∧
      (o.value = blockValuationStep low highCount ∧ out.mem = mem) ∧ cost ≤ 36 := by
  have hlimb : limbValuation low ≤ 4 := by
    interval_cases low <;> decide +kernel
  have hfit : blockValuationStep low highCount < 2^w := by
    unfold blockValuationStep
    split <;> omega
  apply runs_start_le
  unfold blockValuationStepBody
  refine runs_seq_call_le hp (vs := [low]) rfl ?_ ⟨low,rfl,hw,hx⟩ ?_
  · intro a ha
    obtain rfl : a = low := by simpa using ha
    omega
  · intro ret mid pos' hpost
    obtain ⟨hret,hmem⟩ := hpost
    change ret = limbValuation low at hret
    subst ret
    refine runs_ret_le (v := blockValuationStep low highCount) ?_ ⟨rfl,hmem⟩ ?_
    · have hzeroVal : limbValuation 0 = 4 := rfl
      have hw0 : w ≠ 0 := by intro he; subst w; exact (by decide : ¬ 16 ≤ 2 ^ (0 : ℕ)) hw
      have hh : highCount < 2^w := by omega
      by_cases he : low = 0 <;>
        simp [Expr.eval, BinOp.eval, startState, Function.update, he, blockValuationStep,
          hzeroVal, hw0, hh] at hfit ⊢ <;>
        simp [hfit]
    · change 0 + 1 + 24 + 2 + 8 ≤ 36
      decide

/-- Contract for the high-to-low accumulation step. -/
def blockValuationStepContract (w : ℕ) : Contract where
  pre args _ := ∃ low count, args = [low,count] ∧ 16 ≤ 2^w ∧ low < 16 ∧ count+4 < 2^w
  post args mem ret out :=
    ret = blockValuationStep (args.getD 0 0) (args.getD 1 0) ∧ out = mem
  cost _ _ := 36

/-- Link the per-limb scan step to a callable procedure. -/
theorem blockValuationStep_meetsContract {w entry limb : ℕ} {p : Program}
    (he : p.procs[entry]? = some (blockValuationStepBody limb))
    (hp : MeetsContract w p limb (limbValuationContract w)) :
    MeetsContract w p entry (blockValuationStepContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨low,count,rfl,hw,hx,hcount⟩ := hpre
  exact blockValuationStep_runs (ω := ω) hp mem pos low count hw hx hcount

/-- Count the low zero bits in a block, capping the result at its bit width. -/
def blockValuation (mem : ℕ → ℕ) : ℕ → ℕ → ℕ
  | _, 0 => 0
  | a, L+1 => blockValuationStep (mem a) (blockValuation mem (a+1) L)

private theorem limbValuation_le {x : ℕ} (hx : x < 16) : limbValuation x ≤ 4 := by
  interval_cases x <;> decide +kernel

/-- A block valuation never exceeds the block width. -/
theorem blockValuation_le {mem : ℕ → ℕ} {a L : ℕ} (h : Num.Valid mem a 4 L) :
    blockValuation mem a L ≤ 4*L := by
  induction L generalizing a with
  | zero => rfl
  | succ L ih =>
    have hhead : mem a < 16 := by simpa [Num.base] using h 0 (by omega)
    have htail : Num.Valid mem (a+1) 4 L := by
      intro j hj
      simpa [Nat.add_assoc,Nat.add_comm 1] using h (j+1) (by omega)
    have ht := ih htail
    have hh := limbValuation_le hhead
    simp only [blockValuation,blockValuationStep]
    split <;> omega

/-- Starting at the highest limb, extend the scanned suffix by one limb
at each iteration. Registers zero and one hold the block base and width. -/
def blockValuationLoop (entry : ℕ) : Stmt :=
  forRange 3 (.const 0) (.reg 1)
    (.call 2 entry [.load (.bin .add (.reg 0) (.bin .sub (.reg 1)
      (.bin .add (.reg 3) (.const 1)))), .reg 2])

/-- The read-only scan costs linear time in the input limb count. -/
theorem blockValuationLoop_triple {w entry : ℕ} {p : Program}
    (hp : MeetsContract w p entry (blockValuationStepContract w))
    (mem : ℕ → ℕ) (pos a L : ℕ) (hw : 16 ≤ 2^w)
    (ha : a+L < 2^w) (hL : 4*L < 2^w) (hv : Num.Valid mem a 4 L) :
    Triple w p (fun st => st = startState [a,L] mem pos) (blockValuationLoop entry)
      (normalPost fun st => st.mem = mem ∧ st.regs 2 = blockValuation mem a L)
      (fun _ => 55*L+7) := by
  let args : List Expr := [.load (.bin .add (.reg 0) (.bin .sub (.reg 1)
    (.bin .add (.reg 3) (.const 1)))), .reg 2]
  let Inv := fun i (st : State) => st.regs 0 = a ∧ st.regs 1 = L ∧ st.regs 3 = i ∧
    st.mem = mem ∧ st.regs 2 = blockValuation mem (a+(L-i)) i
  have loop := Triple.forRange_const (w := w) (p := p) (r := 3)
    (lo := .const 0) (hi := .reg 1) (body := .call 2 entry args) (Inv := Inv)
    (P := fun st => st = startState [a,L] mem pos)
    46 0 L (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st he => by subst st; exact ⟨by eval_expr, by simp [Inv,startState,blockValuation]⟩)
    (fun _ _ _ _ h => h.2.2.1)
    (fun _ st _ _ h => by have hreg := h.2.1; eval_expr)
    (fun i _ hi st ω ⟨h0,h1,h3,hm,h2⟩ => by
      let offset := L-(i+1)
      let x := mem (a+offset)
      let c := blockValuation mem (a+(L-i)) i
      have ho : offset < L := by dsimp [offset]; omega
      have hx : x < 16 := hv offset ho
      have hv' : Num.Valid mem (a+(L-i)) 4 i := by
        intro j hj
        simpa [Nat.add_assoc] using hv (L-i+j) (by omega)
      have hcount := blockValuation_le hv'
      have hfit : c+4 < 2^w := by dsimp [c]; omega
      have hidx : i+1 < 2^w := by omega
      have haddress : a+offset < 2^w := by omega
      have hoff : offset < 2^w := by omega
      have hmAt : Expr.MemAt st (a+offset) x := congrFun hm _
      have heval : evalArgs w st args = some [x,c] := by
        dsimp [args,x,c,offset] at *
        eval_expr
      obtain ⟨out,cost,ret,hr,hpost,hret,hframe,hcost⟩ :=
        runs_call_of_meetsContract (r := 2) hp heval
          (by intro word hw'; simp at hw'; rcases hw' with rfl | rfl <;> omega)
          ⟨x,c,rfl,hw,hx,hfit⟩ ω
      obtain ⟨hval,hmem⟩ := hpost
      have hbase : a+offset+1 = a+(L-i) := by dsimp [offset]; omega
      refine ⟨.normal,out,cost,hr,⟨⟨?_,?_,by simp,(hmem.trans hm),?_⟩,?_⟩,?_⟩
      · exact (hframe 0 (by decide)).trans h0
      · exact (hframe 1 (by decide)).trans h1
      · change Function.update out.regs 3 (i+1) 2 = _
        rw [Function.update_of_ne (by decide : 2 ≠ 3),hret,hval]
        change blockValuationStep x c = blockValuation mem (a+offset) (i+1)
        rw [blockValuation,hbase]
      · exact (hframe 3 (by decide)).trans h3
      · apply hcost.trans
        change 9+36+1 ≤ 46
        decide)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal => exact ⟨h.2.2.2.1, by simpa using h.2.2.2.2⟩
  · intro st _
    simp only [Nat.sub_zero, Expr.size]
    rw [Nat.mul_comm L]

private theorem lowLimb_dvd_iff {k x tail : ℕ} (hk : k ≤ 4) :
    2^k ∣ x+16*tail ↔ 2^k ∣ x := by
  have hd : (2:ℕ)^k ∣ 16 := Nat.pow_dvd_pow 2 hk
  exact (Nat.dvd_add_iff_left (dvd_mul_of_dvd_left hd tail)).symm

/-- The scan counts exactly the powers of two dividing the decoded
unsigned integer, capped at the number of bits in the block. -/
theorem le_blockValuation_iff {mem : ℕ → ℕ} {a L k : ℕ} (h : Num.Valid mem a 4 L) :
    k ≤ blockValuation mem a L ↔ k ≤ 4*L ∧ 2^k ∣ Num.unsignedVal mem a 4 L := by
  induction L generalizing a k with
  | zero => simp [blockValuation,Num.unsignedVal]
  | succ L ih =>
    have hhead : mem a < 16 := by simpa [Num.base] using h 0 (by omega)
    have htail : Num.Valid mem (a+1) 4 L := by
      intro j hj
      simpa [Nat.add_assoc,Nat.add_comm 1] using h (j+1) (by omega)
    let t := Num.unsignedVal mem (a+1) 4 L
    let v := blockValuation mem (a+1) L
    change k ≤ blockValuationStep (mem a) v ↔ k ≤ 4*(L+1) ∧ 2^k ∣ mem a+16*t
    by_cases hz : mem a = 0
    · rw [hz]
      change k ≤ 4+v ↔ k ≤ 4*(L+1) ∧ 2^k ∣ 0+16*t
      by_cases hk : k ≤ 4
      · exact iff_of_true (by omega) ⟨by omega, (lowLimb_dvd_iff hk).2 (dvd_zero _)⟩
      · have hkp : k = 4+(k-4) := by omega
        have hdiv : (2:ℕ)^k ∣ 0+16*t ↔ 2^(k-4) ∣ t := by
          rw [zero_add, show (2:ℕ)^k = 16*2^(k-4) by
            conv_lhs => rw [hkp,pow_add]
            rfl]
          exact Nat.mul_dvd_mul_iff_left (by decide)
        rw [hdiv]
        have htail' : k-4 ≤ v ↔ k-4 ≤ 4*L ∧ 2^(k-4) ∣ t := ih htail
        constructor
        · intro hv
          obtain ⟨hl,hd⟩ := htail'.1 (by omega)
          exact ⟨by omega,hd⟩
        · rintro ⟨hl,hd⟩
          have hu := htail'.2 ⟨by omega,hd⟩
          omega
    · have hlimb : limbValuation (mem a) ≤ 4 := limbValuation_le hhead
      have he : blockValuationStep (mem a) v = padicValNat 2 (mem a) := by
        simp [blockValuationStep,limbValuation,hz]
      have hval : padicValNat 2 (mem a) ≤ 4 := by simpa [limbValuation,hz] using hlimb
      rw [he]
      constructor
      · intro hk
        exact ⟨by omega, (lowLimb_dvd_iff (hk.trans hval)).2
          ((Nat.pow_dvd_iff_le_padicValNat (by decide) hz).2 hk)⟩
      · rintro ⟨_,hd⟩
        have hk : k ≤ 4 := by
          by_contra! hbad
          have h16 : (16:ℕ) ∣ mem a := (lowLimb_dvd_iff (k := 4) le_rfl).1
            ((Nat.pow_dvd_pow 2 (by omega : 4 ≤ k)).trans hd)
          exact (not_le_of_gt hhead) (Nat.le_of_dvd (Nat.pos_of_ne_zero hz) h16)
        exact (Nat.pow_dvd_iff_le_padicValNat (by decide) hz).1
          ((lowLimb_dvd_iff hk).1 hd)

/-- Return the scan accumulator after visiting the whole input block. -/
def blockValuationBody (step : ℕ) : Stmt :=
  .seq (blockValuationLoop step) (.ret (.reg 2))

/-- The standalone scan returns the greatest capped binary valuation. -/
def blockValuationContract (w : ℕ) : Contract where
  pre args mem := ∃ a L, args = [a,L] ∧ 16 ≤ 2^w ∧ a+L < 2^w ∧
    4*L < 2^w ∧ Num.Valid mem a 4 L
  post args mem ret out := ∃ a L, args = [a,L] ∧ out = mem ∧
    ∀ k, k ≤ ret ↔ k ≤ 4*L ∧ 2^k ∣ Num.unsignedVal mem a 4 L
  cost args _ := 55*args.getD 1 0+10

/-- The installed block scan reads only the caller's length block and
returns its exact capped valuation in linear limb time. -/
theorem blockValuation_meetsContract {w entry step : ℕ} {p : Program}
    (he : p.procs[entry]? = some (blockValuationBody step))
    (hp : MeetsContract w p step (blockValuationStepContract w)) :
    MeetsContract w p entry (blockValuationContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨a,L,rfl,hw,ha,hL,hv⟩ := hpre
  apply runs_start_le
  unfold blockValuationBody
  refine runs_seq_triple_le (blockValuationLoop_triple hp mem pos a L hw ha hL hv) rfl ?_
  intro out ⟨hm,hr⟩
  refine runs_ret_le (v := blockValuation mem a L) (by eval_expr)
    ⟨a,L,rfl,hm,fun _ => le_blockValuation_iff hv⟩ ?_
  change 0+(55*L+7)+1+2 ≤ 55*L+10
  omega

/-- Read a block valuation and lower the current common-shift cap. -/
def lowerLengthShiftBody (block : ℕ) : Stmt :=
  .seq (.call 3 block [.reg 0,.reg 1])
    (.ret (.bin .sub (.reg 2) (.bin .sub (.reg 2) (.reg 3))))

/-- One length block restricts the admissible common shifts by divisibility. -/
theorem lowerLengthShift_runs {w block : ℕ} {p : Program} {ω : ℕ → Bool}
    (hc : MeetsContract w p block (blockValuationContract w))
    (mem : ℕ → ℕ) (pos a L cap : ℕ)
    (hw : 16 ≤ 2^w) (ha : a+L < 2^w) (hL : 4*L < 2^w)
    (hcap : cap ≤ 4*L) (hv : Num.Valid mem a 4 L) :
    ∃ o out cost, Runs w p ω (lowerLengthShiftBody block)
      (startState [a,L,cap] mem pos) o out cost ∧
      (out.mem = mem ∧ ∀ k, k ≤ o.value ↔ k ≤ cap ∧ 2^k ∣ Num.unsignedVal mem a 4 L) ∧
      cost ≤ 55*L+22 := by
  apply runs_start_le
  unfold lowerLengthShiftBody
  refine runs_seq_call_le hc (vs := [a,L]) rfl ?_ ⟨a,L,rfl,hw,ha,hL,hv⟩ ?_
  · intro x hx
    rcases (show x = a ∨ x = L by simpa using hx) with rfl | rfl <;> omega
  · intro ret mid pos' hpost
    obtain ⟨b,N,he,hmem,hdiv⟩ := hpost
    simp only [List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl⟩ := he
    have hdiff : cap-ret < 2^w := by omega
    have hresult : cap-(cap-ret) < 2^w := by omega
    refine runs_ret_le (v := cap-(cap-ret)) (by eval_expr) ⟨hmem,?_⟩ ?_
    · intro k
      have he : cap-(cap-ret) = min cap ret := by omega
      change k ≤ cap-(cap-ret) ↔ _
      rw [he,le_min_iff,hdiv]
      exact ⟨fun h => ⟨h.1,h.2.2⟩, fun h => ⟨h.1,h.1.trans hcap,h.2⟩⟩
    · change 0+2+(55*L+10)+2+6 ≤ 55*L+22
      omega

/-- The per-edge step applies a block's divisibility constraint to the cap. -/
def lowerLengthShiftContract (w : ℕ) : Contract where
  pre args mem := ∃ a L cap, args = [a,L,cap] ∧ 16 ≤ 2^w ∧ a+L < 2^w ∧
    4*L < 2^w ∧ cap ≤ 4*L ∧ Num.Valid mem a 4 L
  post args mem ret out := ∃ a L cap, args = [a,L,cap] ∧ out = mem ∧
    ∀ k, k ≤ ret ↔ k ≤ cap ∧ 2^k ∣ Num.unsignedVal mem a 4 L
  cost args _ := 55*args.getD 1 0+22

/-- The installed per-edge step can be called by the live-edge scan. -/
theorem lowerLengthShift_meetsContract {w entry block : ℕ} {p : Program}
    (he : p.procs[entry]? = some (lowerLengthShiftBody block))
    (hc : MeetsContract w p block (blockValuationContract w)) :
    MeetsContract w p entry (lowerLengthShiftContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨a,L,cap,rfl,hw,ha,hL,hcap,hv⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ :=
    lowerLengthShift_runs (ω := ω) hc mem pos a L cap hw ha hL hcap hv
  exact ⟨o,out,cost,hrun,⟨a,L,cap,rfl,hpost⟩,hcost⟩

/-- Visit the live edge names in a compact array. The length table is
indexed by the original names, and register three holds the current cap. -/
def commonLengthShiftArgs : List Expr :=
  [.bin .add (.reg 1) (.bin .mul (.load (.bin .add (.reg 0) (.reg 5))) (.reg 2)),
    .reg 2,.reg 3]

/-- Scan the named length blocks, without visiting the gaps between names. -/
def commonLengthShiftLoop (entry : ℕ) : Stmt :=
  forRange 5 (.const 0) (.reg 4) (.call 3 entry commonLengthShiftArgs)

/-- The scan returns the greatest common shift bounded by the input
precision, in time linear in the number of live limbs. -/
theorem commonLengthShiftLoop_triple {w entry : ℕ} {p : Program}
    (hp : MeetsContract w p entry (lowerLengthShiftContract w))
    (mem : ℕ → ℕ) (pos names lengths L P m : ℕ) (name : ℕ → ℕ)
    (hw : 16 ≤ 2^w) (hL : 4*L < 2^w) (hP : P ≤ 4*L)
    (hm : names+m < 2^w) (_hl : lengths < 2^w)
    (hblocks : ∀ i < m, mem (names+i) = name i ∧
      lengths+name i*L+L < 2^w ∧ Num.Valid mem (lengths+name i*L) 4 L) :
    Triple w p (fun st => st = startState [names,lengths,L,P,m] mem pos)
      (commonLengthShiftLoop entry)
      (normalPost fun st => st.mem = mem ∧ ∀ k, k ≤ st.regs 3 ↔
        k ≤ P ∧ ∀ i < m, 2^k ∣ Num.unsignedVal mem (lengths+name i*L) 4 L)
      (fun _ => (55*L+42)*m+7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = names ∧ st.regs 1 = lengths ∧ st.regs 2 = L ∧ st.regs 4 = m ∧
    st.regs 5 = i ∧ st.mem = mem ∧
    ∀ k, k ≤ st.regs 3 ↔ k ≤ P ∧
      ∀ j < i, 2^k ∣ Num.unsignedVal mem (lengths+name j*L) 4 L
  have loop := Triple.forRange_const (w := w) (p := p) (r := 5) (lo := .const 0)
    (hi := .reg 4) (body := .call 3 entry commonLengthShiftArgs) (Inv := Inv)
    (P := fun st => st = startState [names,lengths,L,P,m] mem pos) (55*L+33)
    0 m (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st he => by subst st; exact ⟨by eval_expr, by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.1)
    (fun _ st _ _ h => by have hreg := h.2.2.2.1; eval_expr)
    (fun i _ hi st ω ⟨h0,h1,h2,h4,h5,hmem,hinv⟩ => by
      obtain ⟨hn,ha,hvalid⟩ := hblocks i hi
      let addr := lengths+name i*L
      let cap := st.regs 3
      have hcap : cap ≤ 4*L := ((hinv cap).1 le_rfl).1.trans hP
      have hmAt : Expr.MemAt st (names+i) (name i) := (congrFun hmem _).trans hn
      have hnameAddr : names+i < 2^w := by omega
      have hprod : name i*L < 2^w := by omega
      have haddr : addr < 2^w := by dsimp [addr]; omega
      have heval : evalArgs w st commonLengthShiftArgs = some [addr,L,cap] := by
        unfold commonLengthShiftArgs
        dsimp [addr,cap]
        eval_expr
      obtain ⟨out,cost,ret,hr,hpost,hret,hframe,hcost⟩ :=
        runs_call_of_meetsContract (r := 3) hp heval
          (by intro x hx; simp at hx; rcases hx with rfl | rfl | rfl <;> omega)
          ⟨addr,L,cap,rfl,hw,ha,hL,hcap,(hmem.symm ▸ hvalid)⟩ ω
      obtain ⟨a,N,b,he,hm',hdiv⟩ := hpost
      simp only [List.cons.injEq,and_true] at he
      obtain ⟨rfl,rfl,rfl⟩ := he
      refine ⟨.normal,out,cost,hr,⟨⟨?_,?_,?_,?_,by simp,hm'.trans hmem,?_⟩,?_⟩,?_⟩
      · exact (hframe 0 (by decide)).trans h0
      · exact (hframe 1 (by decide)).trans h1
      · exact (hframe 2 (by decide)).trans h2
      · exact (hframe 4 (by decide)).trans h4
      · intro k
        change k ≤ Function.update out.regs 5 (i+1) 3 ↔ _
        rw [Function.update_of_ne (by decide : 3 ≠ 5),hret,hdiv,hmem]
        change (k ≤ st.regs 3 ∧ 2^k ∣ Num.unsignedVal mem addr 4 L) ↔ _
        rw [hinv]
        constructor
        · rintro ⟨⟨hk,hs⟩,hd⟩
          refine ⟨hk,fun j hj => ?_⟩
          by_cases he : j = i
          · subst j
            exact hd
          · exact hs j (by omega)
        · rintro ⟨hk,hs⟩
          exact ⟨⟨hk,fun j hj => hs j (by omega)⟩,hs i (by omega)⟩
      · exact (hframe 5 (by decide)).trans h5
      · apply hcost.trans
        change 10+(55*L+22)+1 ≤ 55*L+33
        omega)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal => exact ⟨h.2.2.2.2.2.1,h.2.2.2.2.2.2⟩
  · intro st _
    simp only [Nat.sub_zero,Expr.size]
    rw [Nat.mul_comm m]

/-- A complete scan of the live nonnegative length blocks gives the
least exact precision of the zero-extended length vector. -/
theorem lengthQueryPrecision_of_namedShift {mem : ℕ → ℕ}
    {lengths L P m shift : ℕ} {E : Finset ℕ} (name : ℕ → ℕ)
    (hname : ∀ e, e ∈ E ↔ ∃ j < m, name j = e)
    (hblock : ∀ e ∈ E, Num.Valid mem (lengths+e*L) 4 L ∧
      0 ≤ Num.intVal mem (lengths+e*L) 4 L)
    (hscan : ∀ k, k ≤ shift ↔ k ≤ P ∧
      ∀ j < m, 2^k ∣ Num.unsignedVal mem (lengths+name j*L) 4 L) :
    lengthQueryPrecision (fun e =>
      if e ∈ E then Num.fixVal mem (lengths+e*L) 4 L P else 0) = P-shift := by
  let a := fun e => if e ∈ E then Num.intVal mem (lengths+e*L) 4 L else 0
  have heq : (fun e => if e ∈ E then Num.fixVal mem (lengths+e*L) 4 L P else 0) =
      fun e => (a e : ℝ)/(2:ℝ)^P := by
    funext e
    by_cases he : e ∈ E <;> simp [a,Num.fixVal,he]
  have hdiv (k : ℕ) :
      (∀ j < m, 2^k ∣ Num.unsignedVal mem (lengths+name j*L) 4 L) ↔
        ∀ e, (2:ℤ)^k ∣ a e := by
    have each (e : ℕ) (he : e ∈ E) :
        2^k ∣ Num.unsignedVal mem (lengths+e*L) 4 L ↔ (2:ℤ)^k ∣ a e := by
      rw [Num.unsignedVal_nonnegative_abs (hblock e he).1 (not_lt.mpr (hblock e he).2)]
      simpa [a,he] using
        (Int.natAbs_dvd_natAbs (a := (2:ℤ)^k)
          (b := Num.intVal mem (lengths+e*L) 4 L))
    constructor
    · intro hs e
      by_cases he : e ∈ E
      · obtain ⟨j,hj,rfl⟩ := (hname e).1 he
        exact (each _ he).1 (hs j hj)
      · simp [a,he]
    · intro hs j hj
      exact (each _ ((hname _).2 ⟨j,hj,rfl⟩)).2 (hs _)
  rw [heq]
  have h := (hscan shift).1 le_rfl
  exact lengthQueryPrecision_of_commonShift a h.1 ((hdiv _).1 h.2)
    (fun k hk hd => (hscan k).2 ⟨hk,(hdiv _).2 hd⟩)

/-- Return the greatest common shift after scanning the named blocks. -/
def commonLengthShiftBody (entry : ℕ) : Stmt :=
  .seq (commonLengthShiftLoop entry) (.ret (.reg 3))

/-- Callable format scan with a read-only frame. -/
def commonLengthShiftContract (w names lengths L P m : ℕ) (name : ℕ → ℕ) : Contract where
  pre args mem := args = [names,lengths,L,P,m] ∧
    16 ≤ 2^w ∧ 4*L < 2^w ∧ P ≤ 4*L ∧ names+m < 2^w ∧ lengths < 2^w ∧
    ∀ i < m, mem (names+i) = name i ∧
      lengths+name i*L+L < 2^w ∧ Num.Valid mem (lengths+name i*L) 4 L
  post _ mem ret out := out = mem ∧ ∀ k, k ≤ ret ↔
    k ≤ P ∧ ∀ i < m, 2^k ∣ Num.unsignedVal mem (lengths+name i*L) 4 L
  cost _ _ := (55*L+42)*m+10

/-- The linked scan returns the common shift and leaves the inputs unchanged. -/
theorem commonLengthShift_meetsContract {w entry lower names lengths L P m : ℕ}
    {p : Program} (name : ℕ → ℕ)
    (he : p.procs[entry]? = some (commonLengthShiftBody lower))
    (hp : MeetsContract w p lower (lowerLengthShiftContract w)) :
    MeetsContract w p entry (commonLengthShiftContract w names lengths L P m name) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨rfl,hw,hL,hP,hm,hl,hblocks⟩ := hpre
  apply runs_start_le
  unfold commonLengthShiftBody
  refine runs_seq_triple_le
    (commonLengthShiftLoop_triple hp mem pos names lengths L P m name
      hw hL hP hm hl hblocks) rfl ?_
  intro out hpost
  refine runs_ret_le (v := out.regs 3) (by eval_expr) hpost ?_
  change 0+((55*L+42)*m+7)+1+2 ≤ (55*L+42)*m+10
  omega

/-- Compute the common query precision, refining the least exact length
precision by the multiplicative-weights grid passed in register five. -/
def queryPrecisionBody (scan : ℕ) : Stmt :=
  .seq (.call 6 scan ((List.range 5).map Expr.reg))
    (.ret (.bin .add (.reg 5) (.bin .sub (.bin .sub (.reg 3) (.reg 6)) (.reg 5))))

/-- A call to the live-edge scan computes the caller-independent
fractional precision for the graph query. -/
theorem queryPrecision_runs {w scan names lengths L P m grid : ℕ}
    {p : Program} {ω : ℕ → Bool} {E : Finset ℕ}
    (name : ℕ → ℕ) (mem : ℕ → ℕ) (pos : ℕ)
    (hp : MeetsContract w p scan (commonLengthShiftContract w names lengths L P m name))
    (hwords : ∀ a ∈ [names,lengths,L,P,m,grid], a < 2^w)
    (hpre : (commonLengthShiftContract w names lengths L P m name).pre
      [names,lengths,L,P,m] mem)
    (hname : ∀ e, e ∈ E ↔ ∃ j < m, name j = e)
    (hblock : ∀ e ∈ E, Num.Valid mem (lengths+e*L) 4 L ∧
      0 ≤ Num.intVal mem (lengths+e*L) 4 L) :
    ∃ o out cost, Runs w p ω (queryPrecisionBody scan)
      (startState [names,lengths,L,P,m,grid] mem pos) o out cost ∧
      (out.mem = mem ∧ o.value = graphQueryPrecision grid (fun e =>
        if e ∈ E then Num.fixVal mem (lengths+e*L) 4 L P else 0)) ∧
      cost ≤ (55*L+42)*m+25 := by
  have hP : P < 2^w := hwords _ (by simp)
  have hgrid : grid < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold queryPrecisionBody
  refine runs_seq_call_le hp (vs := [names,lengths,L,P,m]) rfl ?_ hpre ?_
  · intro a ha
    exact hwords a (List.mem_append_left [grid] ha)
  · intro shift mid pos' hpost
    obtain ⟨hm,hscan⟩ := hpost
    have hprec := lengthQueryPrecision_of_namedShift name hname hblock hscan
    have hsum : grid+(P-shift-grid) = max grid (P-shift) := by omega
    have hs : grid+(P-shift-grid) < 2^w := by omega
    have hdiff : P-shift < 2^w := by omega
    have hdiff' : P-shift-grid < 2^w := by omega
    refine runs_ret_le (v := grid+(P-shift-grid)) (by eval_expr) ⟨hm,?_⟩ ?_
    · rw [hsum,graphQueryPrecision,hprec]
      rfl
    · change 0+5+((55*L+42)*m+10)+2+8 ≤ (55*L+42)*m+25
      omega

/-- Callable common precision for a named length vector. -/
def queryPrecisionContract (w names lengths L P m grid : ℕ)
    (name : ℕ → ℕ) (E : Finset ℕ) : Contract where
  pre args mem := args = [names,lengths,L,P,m,grid] ∧
    (commonLengthShiftContract w names lengths L P m name).pre [names,lengths,L,P,m] mem ∧
    (∀ e, e ∈ E ↔ ∃ j < m, name j = e) ∧
    ∀ e ∈ E, Num.Valid mem (lengths+e*L) 4 L ∧ 0 ≤ Num.intVal mem (lengths+e*L) 4 L
  post _ mem ret out := out = mem ∧ ret = graphQueryPrecision grid (fun e =>
    if e ∈ E then Num.fixVal mem (lengths+e*L) 4 L P else 0)
  cost _ _ := (55*L+42)*m+25

/-- Install the format precision calculator for the graph's live lengths. -/
theorem queryPrecision_meetsContract {w entry scan names lengths L P m grid : ℕ}
    {p : Program} (name : ℕ → ℕ) (E : Finset ℕ)
    (he : p.procs[entry]? = some (queryPrecisionBody scan))
    (hp : MeetsContract w p scan (commonLengthShiftContract w names lengths L P m name)) :
    MeetsContract w p entry (queryPrecisionContract w names lengths L P m grid name E) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨rfl,hscan,hname,hblock⟩ := hpre
  exact queryPrecision_runs (ω := ω) name mem pos hp hwords hscan hname hblock

end MinCostFlow.LastLevelProgram
