module

public import WordRAM.Logic
public import MinCostFlow.Num.Encoding
public import MinCostFlow.LastLevelProgram.CanonicalOracle
import MinCostFlow.LastLevelProgram.ScaleBlock
import MinCostFlow.Num.DivisionSigns
import MinCostFlow.Num.ExtendFacts
import MinCostFlow.Num.WordBounds
import Mathlib.Tactic
import Mathlib.Data.Nat.Size
import WordRAM.Tactic

/-!
# Extracting a bit from the solver format

The guest tree call of Theorem 2.2 (page 7) uses bit limbs. The last-level
builder reads a bit from the corresponding four-bit solver limb before
packing lengths at the canonical query precision.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM

/-- Read a bit using the supplied base address and bit
index arguments, without changing memory. -/
def formatBitBody : Stmt :=
  .ret (.bin .mod
    (.bin .shiftRight (.load (.bin .add (.reg 0) (.bin .div (.reg 1) (.const 4))))
      (.bin .mod (.reg 1) (.const 4))) (.const 2))

/-- The bit reader returns the corresponding binary digit of the stored
limb, at constant cost independent of the limb count. -/
theorem formatBit_runs {w : ℕ} {p : Program} {ω : ℕ → Bool}
    (mem : ℕ → ℕ) (pos base bit : ℕ) (hw : 16 ≤ 2^w)
    (_hbit : bit < 2^w) (haddr : base+bit/4 < 2^w) (hx : mem (base+bit/4) < 16) :
    ∃ o out cost, Runs w p ω formatBitBody (startState [base,bit] mem pos) o out cost ∧
      (o.value = (mem (base+bit/4) >>> (bit%4)) % 2 ∧ out.mem = mem) ∧ cost ≤ 16 := by
  have hdiv : bit/4 < 2^w := by omega
  have hmod : bit%4 < 2^w := by omega
  have hs : (mem (base+bit/4) >>> (bit%4)) < 2^w := by
    rw [Nat.shiftRight_eq_div_pow]
    exact (Nat.div_le_self ..).trans_lt (hx.trans_le hw)
  have hr : (mem (base+bit/4) >>> (bit%4)) % 2 < 2^w :=
    (Nat.mod_lt _ (by decide)).trans_le (by omega)
  have hm : Expr.MemAt (startState [base,bit] mem pos) (base+bit/4) (mem (base+bit/4)) := rfl
  apply runs_start_le
  unfold formatBitBody
  exact runs_ret_le (by eval_expr) ⟨rfl,rfl⟩ (by decide)

/-- Extracting a bit from its four-bit limb agrees with extracting that
position from the entire unsigned block. -/
theorem formatBit_eq_unsignedVal {mem : ℕ → ℕ} {a L bit : ℕ}
    (hv : Num.Valid mem a 4 L) (hbit : bit < 4*L) :
    (mem (a+bit/4) >>> (bit%4)) % 2 = (Num.unsignedVal mem a 4 L / 2^bit) % 2 := by
  let q := bit/4
  let r := bit%4
  have hq : q < L := by dsimp [q]; omega
  have hr : r < 4 := Nat.mod_lt _ (by decide)
  have hsplit : 4*q+r = bit := by dsimp [q,r]; omega
  have hp : (2:ℕ)^bit = Num.capacity 4 q * 2^r := by
    rw [Num.capacity_eq_two_pow, ← pow_add, hsplit]
  have h16 : (2:ℕ)^r ∣ 16 := Nat.pow_dvd_pow 2 hr.le
  obtain ⟨d,hd⟩ := h16
  have hd2 : 2 ∣ d := by
    have hdiv : (2:ℕ)^(r+1) ∣ 16 := Nat.pow_dvd_pow 2 (show r+1 ≤ 4 by omega)
    rw [pow_succ, hd] at hdiv
    exact (Nat.mul_dvd_mul_iff_left (Nat.two_pow_pos _)).1 hdiv
  have htail : Num.unsignedVal mem (a+q) 4 (L-q) =
      mem (a+q)+16*Num.unsignedVal mem ((a+q)+1) 4 (L-q-1) := by
    conv_lhs => rw [show L-q = (L-q-1)+1 by omega]
    rfl
  rw [Nat.shiftRight_eq_div_pow, hp, ← Nat.div_div_eq_div_mul,
    Num.unsignedVal_tail_div hv hq.le, htail, hd]
  rw [Nat.mul_assoc, Nat.add_mul_div_left _ _ (Nat.two_pow_pos _)]
  obtain ⟨u,hu⟩ := hd2
  rw [hu, Nat.mul_assoc, Nat.add_mul_mod_self_left]

/-- Move a nonnegative numerator to a new binary precision. A decrease
in precision drops the low bits, and an increase pads with low zero bits. -/
def rescaleUnsigned (P Q n : ℕ) : ℕ :=
  if P ≤ Q then n * 2^(Q-P) else n / 2^(P-Q)

/-- Each destination bit either lies in the low zero padding or reads
one bit at the aligned source offset. -/
theorem rescaleUnsigned_bit (P Q n i : ℕ) :
    (rescaleUnsigned P Q n / 2^i) % 2 =
      if P+i < Q then 0 else (n / 2^(P+i-Q)) % 2 := by
  unfold rescaleUnsigned
  by_cases hPQ : P ≤ Q
  · rw [ite_eq_left hPQ]
    by_cases hi : P+i < Q
    · rw [ite_eq_left hi]
      have he : Q-P = i+1+(Q-P-(i+1)) := by omega
      have hs : (2:ℕ)^(Q-P) = 2^i * (2 * 2^(Q-P-(i+1))) := by
        conv_lhs => rw [he]
        rw [pow_add,pow_succ]
        ring
      rw [hs, ← Nat.mul_assoc, Nat.mul_comm n (2^i), Nat.mul_assoc,
        Nat.mul_div_cancel_left _ (Nat.two_pow_pos _)]
      exact Nat.mod_eq_zero_of_dvd ⟨n * 2^(Q-P-(i+1)), by ring⟩
    · rw [ite_eq_right hi]
      have he : i = (Q-P)+(P+i-Q) := by omega
      have hs : (2:ℕ)^i = 2^(Q-P)*2^(P+i-Q) := by
        rw [← pow_add,← he]
      rw [hs, ← Nat.div_div_eq_div_mul, Nat.mul_div_cancel _ (Nat.two_pow_pos _)]
  · rw [ite_eq_right hPQ, ite_eq_right (by omega : ¬ P+i < Q),
      Nat.div_div_eq_div_mul, ← pow_add]
    rw [show P-Q+i = P+i-Q by omega]

/-- The source offset for destination bit `i`, using argument words
`[base, L, P, Q, i]`. -/
def conversionOffset : Expr :=
  .bin .sub (.bin .add (.reg 2) (.reg 4)) (.reg 3)

/-- Test whether the aligned bit lies within the source block. -/
def conversionInRange : Expr :=
  .bin .and
    (.bin .eq (.bin .lt (.bin .add (.reg 2) (.reg 4)) (.reg 3)) (.const 0))
    (.bin .lt conversionOffset (.bin .mul (.const 4) (.reg 1)))

/-- Read an aligned source bit, or return zero beyond the block. -/
def conversionBitBody (readBit : ℕ) : Stmt :=
  .cond conversionInRange
    (.seq (.call 5 readBit [.reg 0,conversionOffset]) (.ret (.reg 5)))
    (.ret (.const 0))

/-- Callable readout for the four-bit limb encoding. -/
def formatBitContract (w : ℕ) : Contract where
  pre args mem := ∃ base bit, args = [base,bit] ∧ 16 ≤ 2^w ∧
    base+bit/4 < 2^w ∧ mem (base+bit/4) < 16
  post args mem ret out := ∃ base bit, args = [base,bit] ∧
    ret = (mem (base+bit/4) >>> (bit%4)) % 2 ∧ out = mem
  cost _ _ := 16

/-- The installed bit reader preserves memory. -/
theorem formatBit_meetsContract {w entry : ℕ} {p : Program}
    (he : p.procs[entry]? = some formatBitBody) :
    MeetsContract w p entry (formatBitContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨base,bit,rfl,hw,haddr,hx⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ :=
    formatBit_runs (p := p) (ω := ω) mem pos base bit hw (hwords _ (by simp)) haddr hx
  exact ⟨o,out,cost,hrun,⟨base,bit,rfl,hpost⟩,hcost⟩

/-- The range test evaluates to one exactly when the aligned bit is
present. The test itself never reads any memory cells. -/
theorem conversionInRange_eval {w : ℕ} (mem : ℕ → ℕ) (pos a L P Q i : ℕ)
    (hw : 16 ≤ 2^w) (hs : P+i < 2^w) (_hQ : Q < 2^w) (hL : 4*L < 2^w) :
    Expr.eval w (startState [a,L,P,Q,i] mem pos) conversionInRange =
      some (if Q ≤ P+i ∧ P+i-Q < 4*L then 1 else 0) := by
  have hsub : P+i-Q < 2^w := by omega
  have hw0 : w ≠ 0 := by intro he; subst w; exact (by decide : ¬ 16 ≤ 2 ^ (0 : ℕ)) hw
  by_cases h₁ : P+i < Q <;> by_cases h₂ : P+i-Q < 4*L <;>
    simp [conversionInRange, conversionOffset,Expr.eval,BinOp.eval,startState,
      hs,hL,hsub,hw0,
      show 4 < 2^w by omega,h₁,h₂,show Q ≤ P+i ↔ ¬ P+i < Q by omega]

/-- Conversion returns the selected bit of the rescaled numerator.
Both branches preserve memory, including when the padding case skips the load. -/
theorem conversionBit_runs {w readBit : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp : MeetsContract w p readBit (formatBitContract w))
    (mem : ℕ → ℕ) (pos a L P Q i : ℕ)
    (hw : 16 ≤ 2^w) (hs : P+i < 2^w) (hQ : Q < 2^w) (hL : 4*L < 2^w)
    (ha : a+L < 2^w) (hv : Num.Valid mem a 4 L) :
    ∃ o out cost, Runs w p ω (conversionBitBody readBit)
      (startState [a,L,P,Q,i] mem pos) o out cost ∧
      (o.value = (rescaleUnsigned P Q (Num.unsignedVal mem a 4 L) / 2^i) % 2 ∧
        out.mem = mem) ∧ cost ≤ 48 := by
  let st := startState [a,L,P,Q,i] mem pos
  let bit := P+i-Q
  have he := conversionInRange_eval mem pos a L P Q i hw hs hQ hL
  rw [rescaleUnsigned_bit]
  by_cases h : Q ≤ P+i ∧ bit < 4*L
  · have hh : ¬ P+i < Q := by have := h.1; omega
    rw [ite_eq_right hh]
    have hcond : Expr.eval w st conversionInRange = some 1 := by
      exact he.trans (congrArg some (ite_eq_left h))
    have hidx : bit/4 < L := by have := h.2; omega
    have haddr : a+bit/4 < 2^w := by omega
    have hx : mem (a+bit/4) < 16 := hv _ hidx
    have hsub : bit < 2^w := by dsimp [bit]; omega
    have hargs : evalArgs w st [.reg 0,conversionOffset] = some [a,bit] := by
      dsimp [st,conversionOffset,bit]
      eval_expr
    have hcall : ∃ o out cost, Runs w p ω
          (.seq (.call 5 readBit [.reg 0,conversionOffset]) (.ret (.reg 5))) st o out cost ∧
        (o.value = (Num.unsignedVal mem a 4 L / 2^bit) % 2 ∧ out.mem = mem) ∧ cost ≤ 27 := by
      apply runs_start_le
      refine runs_seq_call_le hp hargs ?_ ⟨a,bit,rfl,hw,haddr,hx⟩ ?_
      · intro x hx'
        rcases (show x = a ∨ x = bit by simpa using hx') with rfl | rfl <;> omega
      · intro ret mid pos' hpost
        obtain ⟨b,k,he',hval,hmem⟩ := hpost
        simp only [List.cons.injEq,and_true] at he'
        obtain ⟨rfl,rfl⟩ := he'
        refine runs_ret_le (v := ret) (by eval_expr) ⟨?_,hmem⟩ ?_
        · exact hval.trans (formatBit_eq_unsignedVal hv h.2)
        · change 0+6+16+2+2 ≤ 27
          decide
    obtain ⟨o,out,c,hrun,hpost,hcost⟩ := hcall
    refine ⟨o,out,conversionInRange.size+c+1,?_,hpost,?_⟩
    · exact runs_cond_iff.mpr ⟨1,c,hcond,by simpa using hrun,rfl⟩
    · change 17+c+1 ≤ 48
      omega
  · have hcond : Expr.eval w st conversionInRange = some 0 := by
      exact he.trans (congrArg some (ite_eq_right h))
    have hzero : (if P+i < Q then 0 else (Num.unsignedVal mem a 4 L / 2^(P+i-Q)) % 2) = 0 := by
      split
      · rfl
      · have hhigh : 4*L ≤ bit := by omega
        have hu := Num.unsignedVal_lt hv
        rw [Num.capacity_eq_two_pow] at hu
        rw [Nat.div_eq_of_lt (hu.trans_le (Nat.pow_le_pow_right (by decide) hhigh))]
    have hret : Runs w p ω (.ret (.const 0)) st (.returned 0) st 2 :=
      runs_ret_iff.mpr ⟨0,by eval_expr,rfl,rfl,rfl⟩
    refine ⟨.returned 0,st,conversionInRange.size+2+1,?_,⟨hzero.symm,rfl⟩,?_⟩
    · exact runs_cond_iff.mpr ⟨0,2,hcond,by simpa using hret,rfl⟩
    · decide

/-- Callable read-only conversion of one destination bit. -/
def conversionBitContract (w : ℕ) : Contract where
  pre args mem := ∃ a L P Q i, args = [a,L,P,Q,i] ∧
    16 ≤ 2^w ∧ P+i < 2^w ∧ Q < 2^w ∧ 4*L < 2^w ∧ a+L < 2^w ∧
    Num.Valid mem a 4 L
  post args mem ret out := ∃ a L P Q i, args = [a,L,P,Q,i] ∧
    ret = (rescaleUnsigned P Q (Num.unsignedVal mem a 4 L) / 2^i) % 2 ∧ out = mem
  cost _ _ := 48

/-- Install the conversion bit reader. -/
theorem conversionBit_meetsContract {w entry readBit : ℕ} {p : Program}
    (he : p.procs[entry]? = some (conversionBitBody readBit))
    (hr : MeetsContract w p readBit (formatBitContract w)) :
    MeetsContract w p entry (conversionBitContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨a,L,P,Q,i,rfl,hw,hs,hQ,hL,ha,hv⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ :=
    conversionBit_runs (ω := ω) hr mem pos a L P Q i hw hs hQ hL ha hv
  exact ⟨o,out,cost,hrun,⟨a,L,P,Q,i,rfl,hpost⟩,hcost⟩

/-- Read one converted bit and store it at the destination offset. -/
def storeConversionBitBody (read : ℕ) : Stmt :=
  .seq (.call 6 read ((List.range 5).map Expr.reg))
    (.seq (.store (.bin .add (.reg 5) (.reg 4)) (.reg 6)) (.ret (.const 0)))

/-- The conversion step changes only the requested destination cell. -/
theorem storeConversionBit_runs {w read : ℕ} {p : Program} {ω : ℕ → Bool}
    (hp : MeetsContract w p read (conversionBitContract w))
    (mem : ℕ → ℕ) (pos a L P Q i dst : ℕ)
    (hw : 16 ≤ 2^w) (hs : P+i < 2^w) (hQ : Q < 2^w)
    (hL : 4*L < 2^w) (ha : a+L < 2^w)
    (hv : Num.Valid mem a 4 L) (hd : dst+i < 2^w) :
    ∃ o out cost, Runs w p ω (storeConversionBitBody read)
      (startState [a,L,P,Q,i,dst] mem pos) o out cost ∧
      (o.value = 0 ∧ out.mem = Function.update mem (dst+i)
        ((rescaleUnsigned P Q (Num.unsignedVal mem a 4 L) / 2^i) % 2)) ∧
      cost ≤ 64 := by
  apply runs_start_le
  unfold storeConversionBitBody
  refine runs_seq_call_le hp (vs := [a,L,P,Q,i]) rfl ?_
    ⟨a,L,P,Q,i,rfl,hw,hs,hQ,hL,ha,hv⟩ ?_
  · intro x hx
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> omega
  · intro ret mid pos' hpost
    obtain ⟨b,N,R,S,k,he,hret,hmem⟩ := hpost
    simp only [List.cons.injEq,and_true] at he
    obtain ⟨rfl,rfl,rfl,rfl,rfl⟩ := he
    have hfit : ret < 2^w := by
      rw [hret]
      exact (Nat.mod_lt _ (by decide)).trans_le (by omega)
    refine runs_seq_store_le (x := dst+i) (v := ret) (by eval_expr) (by eval_expr) ?_
    refine runs_ret_le (v := 0) (by eval_expr) ⟨rfl,?_⟩ ?_
    · exact congrArg (fun (m : ℕ → ℕ) => Function.update m (dst+i) ret) hmem |>.trans
        (congrArg (Function.update mem (dst+i)) hret)
    · change 0+5+48+2+3+1+2+2 ≤ 64
      decide

/-- Callable single-cell writer for precision conversion. -/
def storeConversionBitContract (w : ℕ) : Contract where
  pre args mem := ∃ a L P Q i dst, args = [a,L,P,Q,i,dst] ∧
    16 ≤ 2^w ∧ P+i < 2^w ∧ Q < 2^w ∧ 4*L < 2^w ∧ a+L < 2^w ∧
    Num.Valid mem a 4 L ∧ dst+i < 2^w
  post args mem ret out := ∃ a L P Q i dst, args = [a,L,P,Q,i,dst] ∧
    ret = 0 ∧ out = Function.update mem (dst+i)
      ((rescaleUnsigned P Q (Num.unsignedVal mem a 4 L) / 2^i) % 2)
  cost _ _ := 64

/-- Install the single-cell conversion writer. -/
theorem storeConversionBit_meetsContract {w entry read : ℕ} {p : Program}
    (he : p.procs[entry]? = some (storeConversionBitBody read))
    (hp : MeetsContract w p read (conversionBitContract w)) :
    MeetsContract w p entry (storeConversionBitContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨a,L,P,Q,i,dst,rfl,hw,hs,hQ,hL,ha,hv,hd⟩ := hpre
  obtain ⟨o,out,cost,hrun,hpost,hcost⟩ :=
    storeConversionBit_runs (ω := ω) hp mem pos a L P Q i dst hw hs hQ hL ha hv hd
  exact ⟨o,out,cost,hrun,⟨a,L,P,Q,i,dst,rfl,hpost⟩,hcost⟩

/-- Visit the destination bits in increasing order. The argument words
are the source, source width, two precisions, destination, and destination width. -/
def conversionBlockLoop (entry : ℕ) : Stmt :=
  forRange 6 (.const 0) (.reg 5)
    (.call 7 entry [.reg 0,.reg 1,.reg 2,.reg 3,.reg 6,.reg 4])

/-- Conversion writes every guest bit and frames the source and all
other memory. Its cost is linear in the destination limb count. -/
theorem conversionBlockLoop_triple {w entry : ℕ} {p : Program}
    (hp : MeetsContract w p entry (storeConversionBitContract w))
    (mem : ℕ → ℕ) (pos a L P Q dst N : ℕ)
    (hw : 16 ≤ 2^w) (hs : P+N < 2^w) (hQ : Q < 2^w)
    (hL : 4*L < 2^w) (ha : a+L ≤ dst) (hd : dst+N < 2^w)
    (hv : Num.Valid mem a 4 L) :
    let value := rescaleUnsigned P Q (Num.unsignedVal mem a 4 L)
    Triple w p (fun st => st = startState [a,L,P,Q,dst,N] mem pos)
      (conversionBlockLoop entry)
      (normalPost fun st =>
        (∀ i < N, st.mem (dst+i) = (value/2^i)%2) ∧
        ∀ b, b < dst ∨ dst+N ≤ b → st.mem b = mem b)
      (fun _ => 80*N+7) := by
  intro value
  let Inv := fun i (st : State) =>
    st.regs 0 = a ∧ st.regs 1 = L ∧ st.regs 2 = P ∧ st.regs 3 = Q ∧
    st.regs 4 = dst ∧ st.regs 5 = N ∧ st.regs 6 = i ∧
    (∀ j < i, st.mem (dst+j) = (value/2^j)%2) ∧
    ∀ b, b < dst ∨ dst+i ≤ b → st.mem b = mem b
  have loop := Triple.forRange_const (w := w) (p := p) (r := 6)
    (lo := .const 0) (hi := .reg 5)
    (body := .call 7 entry [.reg 0,.reg 1,.reg 2,.reg 3,.reg 6,.reg 4])
    (Inv := Inv) (P := fun st => st = startState [a,L,P,Q,dst,N] mem pos)
    71 0 N (Nat.zero_le _) (by omega) (fun _ => by omega)
    (fun st he => by subst st; exact ⟨by eval_expr, by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.2.1)
    (fun _ st _ _ h => by have hreg := h.2.2.2.2.2.1; eval_expr)
    (fun i _ hi st ω ⟨h0,h1,h2,h3,h4,h5,h6,hdone,hframe⟩ => by
      have hsrc : ∀ j < L, st.mem (a+j) = mem (a+j) :=
        fun j hj => hframe _ (Or.inl (by omega))
      have hv' : Num.Valid st.mem a 4 L := fun j hj => (hsrc j hj).trans_lt (hv j hj)
      have hargs : evalArgs w st [.reg 0,.reg 1,.reg 2,.reg 3,.reg 6,.reg 4] =
          some [a,L,P,Q,i,dst] := by eval_expr
      obtain ⟨out,cost,ret,hr,hpost,_,hrf,hcost⟩ :=
        runs_call_of_meetsContract (r := 7) hp hargs
          (by
            intro x hx
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
            rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
          ⟨a,L,P,Q,i,dst,rfl,hw,by omega,hQ,hL,by omega,hv',by omega⟩ ω
      obtain ⟨b,M,S,T,j,d,he,_,hout⟩ := hpost
      simp only [List.cons.injEq,and_true] at he
      obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := he
      rw [Num.unsignedVal_congr hsrc] at hout
      refine ⟨.normal,out,cost,hr,⟨⟨(hrf 0 (by decide)).trans h0,
        (hrf 1 (by decide)).trans h1,(hrf 2 (by decide)).trans h2,
        (hrf 3 (by decide)).trans h3,(hrf 4 (by decide)).trans h4,
        (hrf 5 (by decide)).trans h5,by simp,?_,?_⟩,
        (hrf 6 (by decide)).trans h6⟩,?_⟩
      · intro j hj
        change out.mem (dst+j) = _
        rw [hout]
        by_cases he' : j = i
        · subst j
          exact Function.update_self ..
        · rw [Function.update_of_ne (by omega)]
          exact hdone j (by omega)
      · intro b hb
        change out.mem b = _
        rw [hout,Function.update_of_ne (by omega)]
        exact hframe b (hb.imp_right (by omega))
      · apply hcost.trans
        change 6+64+1 ≤ 71
        decide)
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal => exact h.2.2.2.2.2.2.2
  · intro st _
    simp only [Nat.sub_zero,Expr.size]
    rw [Nat.mul_comm N]

private theorem oneBitDigits_get (N n i : ℕ) (hi : i < N) :
    (Num.digits 1 N n)[i]'(by simpa using hi) = (n/2^i)%2 := by
  induction N generalizing n i with
  | zero => omega
  | succ N ih =>
    cases i with
    | zero => simp [Num.digits,Num.base]
    | succ i =>
      have hi' : i < N := by omega
      change (n % 2 :: Num.digits 1 N (n/2))[i+1]'(by simpa using hi) = _
      rw [List.getElem_cons_succ,ih _ _ hi']
      rw [Nat.div_div_eq_div_mul,pow_succ']

/-- The written destination bits are the canonical signed encoding
whenever its nonnegative numerator fits in the destination block. -/
theorem convertedBits_listAt {mem : ℕ → ℕ} {dst N n : ℕ}
    (hfit : Num.Fits 1 N (n : ℤ))
    (hbits : ∀ i < N, mem (dst+i) = (n/2^i)%2) :
    ListAt mem dst (Num.encodeLimbs 1 N (n : ℤ)) := by
  have hn : n < Num.capacity 1 N := by
    have h := hfit.2
    change 2 * (n : ℤ) < (Num.capacity 1 N : ℤ) at h
    exact_mod_cast (show (n : ℤ) < (Num.capacity 1 N : ℤ) by omega)
  have hr : Num.residue 1 N (n : ℤ) = n := by
    unfold Num.residue
    rw [Int.emod_eq_of_lt (Int.natCast_nonneg _) (by exact_mod_cast hn)]
    simp
  rw [Num.encodeLimbs,hr]
  intro i hi
  have hi' : i < N := by simpa using hi
  exact (hbits i hi').trans (oneBitDigits_get N n i hi').symm

/-- Write a complete guest block and return zero. -/
def conversionBlockBody (store : ℕ) : Stmt :=
  .seq (conversionBlockLoop store) (.ret (.const 0))

/-- The block converter writes exactly the encoding expected by the guest. -/
def conversionBlockContract (w : ℕ) : Contract where
  pre args mem := ∃ a L P Q dst N, args = [a,L,P,Q,dst,N] ∧
    16 ≤ 2^w ∧ P+N < 2^w ∧ Q < 2^w ∧ 4*L < 2^w ∧
    a+L ≤ dst ∧ dst+N < 2^w ∧ Num.Valid mem a 4 L ∧
    Num.Fits 1 N (rescaleUnsigned P Q (Num.unsignedVal mem a 4 L) : ℤ)
  post args mem ret out := ∃ a L P Q dst N, args = [a,L,P,Q,dst,N] ∧
    ret = 0 ∧ ListAt out dst
      (Num.encodeLimbs 1 N (rescaleUnsigned P Q (Num.unsignedVal mem a 4 L) : ℤ)) ∧
    ∀ b, b < dst ∨ dst+N ≤ b → out b = mem b
  cost args _ := 80*args.getD 5 0+10

/-- Install the converter with a canonical guest encoding and a frame
outside the destination. -/
theorem conversionBlock_meetsContract {w entry store : ℕ} {p : Program}
    (he : p.procs[entry]? = some (conversionBlockBody store))
    (hp : MeetsContract w p store (storeConversionBitContract w)) :
    MeetsContract w p entry (conversionBlockContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨a,L,P,Q,dst,N,rfl,hw,hs,hQ,hL,ha,hd,hv,hfit⟩ := hpre
  apply runs_start_le
  unfold conversionBlockBody
  refine runs_seq_triple_le (conversionBlockLoop_triple hp mem pos a L P Q dst N
    hw hs hQ hL ha hd hv) rfl ?_
  intro out ⟨hbits,hframe⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨a,L,P,Q,dst,N,rfl,rfl,convertedBits_listAt hfit hbits,hframe⟩ ?_
  change 0+(80*N+7)+1+2 ≤ 80*N+10
  omega

/-- For a nonnegative solver length the rescaled unsigned numerator
is exactly the floor numerator used by the canonical oracle. -/
theorem rescaleUnsigned_eq_queryNumerator {mem : ℕ → ℕ} {a L P Q : ℕ}
    (hv : Num.Valid mem a 4 L) (hn : 0 ≤ Num.intVal mem a 4 L) :
    (rescaleUnsigned P Q (Num.unsignedVal mem a 4 L) : ℤ) =
      queryNumerator Q (Num.fixVal mem a 4 L P) := by
  let n := Num.unsignedVal mem a 4 L
  have hnum : (n : ℤ) = Num.intVal mem a 4 L := by
    dsimp [n]
    rw [Num.unsignedVal_nonnegative_abs hv (not_lt.mpr hn), Int.natAbs_of_nonneg hn]
  by_cases hPQ : P ≤ Q
  · rw [rescaleUnsigned,ite_eq_left hPQ,queryNumerator_of_shift hPQ]
    change ((n * 2^(Q-P) : ℕ) : ℤ) = _
    push_cast
    rw [hnum]
  · rw [rescaleUnsigned,ite_eq_right hPQ]
    have hpow : (2 : ℝ)^P = (2 : ℝ)^Q * (2 : ℝ)^(P-Q) := by
      rw [← pow_add,Nat.add_sub_of_le (by omega : Q ≤ P)]
    have hcancel : Num.fixVal mem a 4 L P * (2 : ℝ)^Q =
        (n : ℝ) / (2 : ℝ)^(P-Q) := by
      rw [Num.fixVal, ← hnum,hpow,Int.cast_natCast]
      field_simp
    rw [queryNumerator_def,hcancel]
    have hfloor : ⌊(n : ℝ) / (2 : ℝ)^(P-Q)⌋ =
        ((n : ℤ) / (2 : ℤ)^(P-Q)) := by
      simpa only [Int.cast_pow,Int.cast_ofNat,Int.floor_natCast] using
        (Int.floor_div_cast_of_nonneg (show (0:ℤ) ≤ 2^(P-Q) by positivity) (n : ℝ))
    rw [hfloor]
    change ((n / 2^(P-Q) : ℕ) : ℤ) = _
    norm_cast

/-- The length-block interface uses the same numerator as the canonical
oracle after decoding the caller's nonnegative fixed-point length. -/
def guestLengthBlockContract (w : ℕ) : Contract where
  pre args mem := ∃ a L P Q dst N, args = [a,L,P,Q,dst,N] ∧
    16 ≤ 2^w ∧ P+N < 2^w ∧ Q < 2^w ∧ 4*L < 2^w ∧
    a+L ≤ dst ∧ dst+N < 2^w ∧ Num.Valid mem a 4 L ∧
    0 ≤ Num.intVal mem a 4 L ∧ Num.Fits 1 N (queryNumerator Q (Num.fixVal mem a 4 L P))
  post args mem ret out := ∃ a L P Q dst N, args = [a,L,P,Q,dst,N] ∧
    ret = 0 ∧ ListAt out dst
      (Num.encodeLimbs 1 N (queryNumerator Q (Num.fixVal mem a 4 L P))) ∧
    ∀ b, b < dst ∨ dst+N ≤ b → out b = mem b
  cost args _ := 80*args.getD 5 0+10

/-- The same installed converter packs length numerators for the
canonical guest, at a precision supplied as a runtime word. -/
theorem guestLengthBlock_meetsContract {w entry : ℕ} {p : Program}
    (hp : MeetsContract w p entry (conversionBlockContract w)) :
    MeetsContract w p entry (guestLengthBlockContract w) := by
  intro args mem pos ω hwords hpre
  obtain ⟨a,L,P,Q,dst,N,rfl,hw,hs,hQ,hL,ha,hd,hv,hn,hfit⟩ := hpre
  have he := rescaleUnsigned_eq_queryNumerator (P := P) (Q := Q) hv hn
  obtain ⟨body,hbody,o,out,c,hrun,hpost,hcost⟩ :=
    hp [a,L,P,Q,dst,N] mem pos ω hwords
      ⟨a,L,P,Q,dst,N,rfl,hw,hs,hQ,hL,ha,hd,hv,he.symm ▸ hfit⟩
  obtain ⟨b,M,R,S,d,K,hargs,hret,hval,hframe⟩ := hpost
  simp only [List.cons.injEq,and_true] at hargs
  obtain ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩ := hargs
  exact ⟨body,hbody,o,out,c,hrun,⟨a,L,P,Q,dst,N,rfl,hret,he ▸ hval,hframe⟩,hcost⟩

private theorem size_div_twoPow (n k : ℕ) : (n / 2^k).size = n.size-k := by
  have hl (j : ℕ) : j < (n/2^k).size ↔ j < n.size-k := by
    rw [Nat.lt_size,Nat.le_div_iff_mul_le (Nat.two_pow_pos _),← pow_add,← Nat.lt_size]
    omega
  exact le_antisymm
    (Nat.le_of_not_gt fun h => (Nat.lt_irrefl _ ((hl _).1 h)))
    (Nat.le_of_not_gt fun h => (Nat.lt_irrefl _ ((hl _).2 h)))

/-- For positive lengths, rescaling adjusts the bit count by the
difference in precisions. No multiword shift is needed to find the width. -/
theorem rescaleUnsigned_size (P Q n : ℕ) (hn : n ≠ 0) :
    (rescaleUnsigned P Q n).size = n.size+Q-P := by
  by_cases h : P ≤ Q
  · rw [rescaleUnsigned,ite_eq_left h,← Nat.shiftLeft_eq, Nat.size_shiftLeft hn]
    omega
  · rw [rescaleUnsigned,ite_eq_right h,size_div_twoPow]
    omega

/-- The target numerator bit count can be recovered directly from the
unsigned digits of a positive solver length. -/
theorem queryNumerator_size_of_positiveBlock {mem : ℕ → ℕ} {a L P Q : ℕ}
    (hv : Num.Valid mem a 4 L) (hn : 0 < Num.intVal mem a 4 L) :
    (queryNumerator Q (Num.fixVal mem a 4 L P)).natAbs.size =
      (Num.unsignedVal mem a 4 L).size+Q-P := by
  rw [← rescaleUnsigned_eq_queryNumerator hv hn.le,Int.natAbs_natCast]
  apply rescaleUnsigned_size
  rw [Num.unsignedVal_nonnegative_abs hv (not_lt.mpr hn.le)]
  exact Int.natAbs_ne_zero.mpr (ne_of_gt hn)

end MinCostFlow.LastLevelProgram
