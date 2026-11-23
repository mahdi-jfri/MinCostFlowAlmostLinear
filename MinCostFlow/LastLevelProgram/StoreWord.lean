module

public import MinCostFlow.Num.Encoding
public import WordRAM.Logic
import WordRAM.Tactic

/-!
# Writing the integer scale into a limb block

The update scale for Definition 5.8 (pages 19–20) is first computed
as a word. Store its digits from low to high, dividing the remaining
word by the limb base after each digit.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open Num WordRAM

/-- Arguments are the destination, the limb count, and the word to encode. -/
def storeWordLoop (h : ℕ) : Stmt :=
  forRange 3 (.const 0) (.reg 1)
    (.store (.bin .add (.reg 0) (.reg 3)) (.bin .mod (.reg 2) (.const (base h))) ;;
      .assign 2 (.bin .div (.reg 2) (.const (base h))))

private theorem digit_eq (h L x j : ℕ) (hj : j < L) :
    (digits h L x)[j]'(by simpa using hj) = (x / base h ^ j) % base h := by
  induction j generalizing x L with
  | zero =>
    cases L with
    | zero => exact (Nat.not_lt_zero _ hj).elim
    | succ L => simp [digits]
  | succ j ih =>
    cases L with
    | zero => exact (Nat.not_lt_zero _ hj).elim
    | succ L =>
      have hj' := Nat.lt_of_succ_lt_succ hj
      change (digits h L (x / base h))[j]'(by simpa using hj') =
        (x / base h^(j + 1)) % base h
      rw [ih L (x / base h) hj', Nat.div_div_eq_div_mul, pow_succ']

/-- The linear pass writes the exact limb digits and only touches the
destination block. -/
theorem storeWordLoop_triple {w : ℕ} (p : Program) (mem : ℕ → ℕ)
    (pos dst L h x : ℕ) (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hx : x < 2 ^ w) (hroom : dst + L < 2 ^ w) :
    Triple w p (fun st => st = startState [dst,L,x] mem pos) (storeWordLoop h)
      (normalPost fun st => st.regs 0 = dst ∧ st.regs 1 = L ∧
        ListAt st.mem dst (digits h L x) ∧
        (∀ a, a < dst ∨ dst + L ≤ a → st.mem a = mem a))
      (fun _ => 21 * L + 7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = dst ∧ st.regs 1 = L ∧ st.regs 2 = x / base h ^ i ∧ st.regs 3 = i ∧
    (∀ j < i, st.mem (dst + j) = (x / base h^j) % base h) ∧
    (∀ a, a < dst ∨ dst + i ≤ a → st.mem a = mem a)
  have loop := Triple.forRange_const (p := p) (r := 3) (lo := .const 0) (hi := .reg 1)
    (body := .store (.bin .add (.reg 0) (.reg 3)) (.bin .mod (.reg 2) (.const (base h))) ;;
      .assign 2 (.bin .div (.reg 2) (.const (base h))))
    (Inv := Inv) (P := fun st => st = startState [dst,L,x] mem pos)
    12 0 L (Nat.zero_le _) hw (fun _ => by omega)
    (fun st hst => by
      subst st
      refine ⟨by eval_expr, ?_⟩
      dsimp [Inv]
      simp [startState])
    (fun _ _ _ _ h => h.2.2.2.1)
    (fun _ st _ _ h => by
      have hreg : st.regs 1 = L := h.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,hdone,hframe⟩
      let rem := x / base h^i
      let first := { st with mem := Function.update st.mem (dst + i) (rem % base h) }
      let after := { first with regs := Function.update first.regs 2 (rem / base h) }
      have hr : rem < 2 ^ w := (Nat.div_le_self _ _).trans_lt hx
      have hrem : rem % base h < 2 ^ w := (Nat.mod_lt _ (base_pos h)).trans hb
      have hnext : rem / base h < 2 ^ w := (Nat.div_le_self _ _).trans_lt hr
      have had : dst + i < 2 ^ w := by omega
      have hdst : dst < 2 ^ w := by omega
      have hiw : i < 2 ^ w := by omega
      have hstore : Runs w p ω
          (.store (.bin .add (.reg 0) (.reg 3)) (.bin .mod (.reg 2) (.const (base h))))
          st .normal first 7 :=
        runs_store_iff.mpr ⟨dst+i,rem % base h,by eval_expr,by eval_expr,rfl,rfl,rfl⟩
      have hassign : Runs w p ω (.assign 2 (.bin .div (.reg 2) (.const (base h))))
          first .normal after 4 := by
        have hreg : first.regs 2 = rem := h2
        exact runs_assign_iff.mpr ⟨rem / base h,by eval_expr,rfl,rfl,rfl⟩
      refine ⟨.normal, after, 12,
        runs_seq_iff.mpr (Or.inr ⟨first,7,4,hstore,hassign,rfl⟩), ?_, le_rfl⟩
      refine ⟨⟨h0,h1,?_,by simp [after],?_,?_⟩,h3⟩
      · simp [after, rem, Nat.div_div_eq_div_mul, pow_succ]
      · intro j hj
        change Function.update st.mem (dst + i) (rem % base h) (dst+j) = _
        by_cases hji : j = i
        · subst j
          simp [rem]
        · rw [Function.update_of_ne (by omega)]
          exact hdone j (by omega)
      · intro a ha
        change Function.update st.mem (dst + i) (rem % base h) a = _
        rw [Function.update_of_ne (by omega)]
        exact hframe a (ha.imp_right (by omega)))
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st hout
    cases o with
    | returned _ => exact hout
    | normal =>
      obtain ⟨h0,h1,_,_,hnum,hframe⟩ := hout
      refine ⟨h0,h1,?_,hframe⟩
      intro j hj
      have hj' : j < L := by simpa using hj
      exact (hnum j hj').trans (digit_eq h L x j hj').symm
  · intro _ _
    simp [Expr.size_const, Expr.size_reg, Nat.mul_comm]

/-- When the word fits the signed width, the emitted digits give a
valid block with exactly that signed value. -/
theorem storeWord_value {mem : ℕ → ℕ} {h L dst x : ℕ}
    (hat : ListAt mem dst (digits h L x)) (hfit : Fits h L (x : ℤ)) :
    Valid mem dst h L ∧ intVal mem dst h L = (x : ℤ) := by
  have hx : x < capacity h L := by
    have hb := hfit.2
    exact_mod_cast (show (x : ℤ) < capacity h L by omega)
  have hat' : ListAt mem dst (encodeLimbs h L (x : ℤ)) := by
    simpa only [encodeLimbs, residue_natCast, Nat.mod_eq_of_lt hx] using hat
  exact ⟨valid_encodeLimbs hat', intVal_encodeLimbs hat' hfit⟩

/-- Write the word and return the end of its allocation. -/
def storeWordBody (h : ℕ) : Stmt :=
  storeWordLoop h ;; .ret (.bin .add (.reg 0) (.reg 1))

/-- The heap interface for writing a fitting natural word as a signed block. -/
def storeWordContract (w h : ℕ) : Contract where
  pre args mem := ∃ heap L x, args = [heap,L,x] ∧ Fits h L (x : ℤ) ∧
      ZeroFrom mem heap ∧ heap + L < 2 ^ w
  post args mem ret out :=
    let heap := args.getD 0 0
    let L := args.getD 1 0
    ret = heap + L ∧ (∀ a < heap, out a = mem a) ∧ ZeroFrom out ret ∧
      Valid out heap h L ∧ intVal out heap h L = (args.getD 2 0 : ℤ)
  cost args _ := 21 * args.getD 1 0 + 12

/-- Make the word-to-limbs pass available as a callable procedure. -/
theorem storeWord_meetsContract {w h entry : ℕ} {p : Program}
    (hw : 1 < 2 ^ w) (hb : base h < 2 ^ w)
    (hp : p.procs[entry]? = some (storeWordBody h)) :
    MeetsContract w p entry (storeWordContract w h) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨heap,L,x,rfl,hfit,hzero,hroom⟩ := hpre
  have hx := hwords x (by simp)
  apply runs_start_le
  unfold storeWordBody
  refine runs_seq_triple_le (storeWordLoop_triple p mem pos heap L h x hw hb hx hroom) rfl ?_
  intro st ⟨h0,h1,hlist,hframe⟩
  have ⟨hvalid,hvalue⟩ := storeWord_value hlist hfit
  have hh : heap < 2 ^ w := by omega
  have hL : L < 2 ^ w := by omega
  refine runs_ret_le (v := heap + L) (by eval_expr) ?_ ?_
  · exact ⟨rfl, fun a ha => hframe a (Or.inl ha),
      fun a ha => (hframe a (Or.inr ha)).trans (hzero a (show heap ≤ a from (Nat.le_add_right heap L).trans ha)),hvalid,hvalue⟩
  · simp [storeWordContract, Expr.size]

end MinCostFlow.LastLevelProgram
