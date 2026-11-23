module

public import MinCostFlow.Num.Encoding
public import WordRAM.Logic
public import MinCostFlow.MinRatio.Layouts
public import MinCostFlow.LastLevelProgram.IndexGraph
public import WordRAM.CopyWords
import WordRAM.Tactic

/-!
# Initializing the unit weights

Lemma 5.5 (page 18) starts with weight one at each edge. In the
one-bit limb format, fresh memory needs just one store per edge
to write the numerator of one at the chosen precision.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open Num WordRAM

/-- Write the unit weight bit at offset `P` of each fresh block.
Arguments are `[heap, L, m, P]`. -/
def unitWeightsLoop : Stmt :=
  forRange 4 (.const 0) (.reg 2)
    (.store (.bin .add (.bin .add (.reg 0) (.bin .mul (.reg 4) (.reg 1))) (.reg 3))
      (.const 1))

private theorem unitUnsigned {mem : ℕ → ℕ} {a L P : ℕ} (hP : P < L)
    (hmem : ∀ k < L, mem (a + k) = if k = P then 1 else 0) :
    unsignedVal mem a 1 L = 2^P := by
  induction L generalizing a P with
  | zero => exact (Nat.not_lt_zero _ hP).elim
  | succ L ih =>
    cases P with
    | zero =>
      have hhead : mem a = 1 := by simpa using hmem 0 (by omega)
      have htail : unsignedVal mem (a + 1) 1 L = 0 := by
        apply unsignedVal_zero
        intro k hk
        simpa [Nat.add_assoc, Nat.add_comm 1] using hmem (k+1) (by omega)
      rw [unsignedVal, hhead, htail]
      simp
    | succ P =>
      have hhead : mem a = 0 := by simpa using hmem 0 (by omega)
      have htail : unsignedVal mem (a + 1) 1 L = 2^P := by
        apply ih (by omega)
        intro k hk
        simpa [Nat.add_assoc, Nat.add_comm 1] using hmem (k+1) (by omega)
      rw [unsignedVal, hhead, htail, base, pow_one, pow_succ']
      exact zero_add _

/-- A block with exactly the scale bit set decodes to one. -/
theorem unitWeight_value {mem : ℕ → ℕ} {a L P : ℕ} (hP : P + 1 < L)
    (hmem : ∀ k < L, mem (a + k) = if k = P then 1 else 0) :
    Valid mem a 1 L ∧ fixVal mem a 1 L P = 1 := by
  have hcap : 2 * (2^P : ℕ) < capacity 1 L := by
    rw [capacity, base, pow_one, ← pow_succ']
    exact Nat.pow_lt_pow_right (by decide) hP
  have hsign : ¬ capacity 1 L ≤ 2 * (2^P : ℕ) := not_le_of_gt hcap
  refine ⟨fun k hk => ?_, ?_⟩
  · rw [hmem k hk]
    split <;> decide
  · rw [fixVal, intVal, unitUnsigned (by omega) hmem, signedVal, ite_eq_right hsign, sub_zero]
    push_cast
    exact div_self (by positivity)

/-- Initialize the whole table in linear time in the number of edges.
The space is zero on entry, and memory outside the table is preserved. -/
theorem unitWeightsLoop_triple {w : ℕ} (p : Program) (mem : ℕ → ℕ)
    (pos heap L m P : ℕ) (hw : 1 < 2^w) (hm : m < 2^w) (hL : L < 2^w)
    (hP : P + 1 < L) (hz : ZeroFrom mem heap) (hroom : heap + m * L < 2^w) :
    Triple w p (fun st => st = startState [heap,L,m,P] mem pos) unitWeightsLoop
      (normalPost fun st =>
        (st.regs 0 = heap ∧ st.regs 1 = L ∧ st.regs 2 = m) ∧
        (∀ i < m, Valid st.mem (heap + i * L) 1 L ∧ fixVal st.mem (heap + i * L) 1 L P = 1) ∧
        (∀ a < heap, st.mem a = mem a) ∧ ZeroFrom st.mem (heap + m * L))
      (fun _ => 18 * m + 7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = heap ∧ st.regs 1 = L ∧ st.regs 2 = m ∧ st.regs 3 = P ∧ st.regs 4 = i ∧
    (∀ j < i, ∀ k < L, st.mem (heap + j * L + k) = if k = P then 1 else 0) ∧
    (∀ a, a < heap ∨ heap + i * L ≤ a → st.mem a = mem a)
  have loop := Triple.forRange_const (p := p) (r := 4) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add (.bin .add (.reg 0) (.bin .mul (.reg 4) (.reg 1))) (.reg 3))
      (.const 1))
    (Inv := Inv) (P := fun st => st = startState [heap,L,m,P] mem pos)
    9 0 m (Nat.zero_le _) hw (fun _ => hm)
    (fun st hst => by subst st; exact ⟨by eval_expr, by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.1)
    (fun _ st _ _ h => by
      have hr : st.regs 2 = m := h.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,h4,hdone,hframe⟩
      have hmul := Nat.mul_le_mul_right L hi
      rw [Nat.succ_mul] at hmul
      have haddr : heap + i * L + P < 2^w := by omega
      have hprod : i * L < 2^w := by omega
      have hoff : heap + i * L < 2^w := by omega
      have hheap : heap < 2^w := by omega
      have hi' : i < 2^w := by omega
      have hp' : P < 2^w := by omega
      refine ⟨.normal, { st with mem := Function.update st.mem (heap + i * L + P) 1 },
        9, runs_store_iff.mpr ⟨_,1,by eval_expr,by eval_expr,rfl,rfl,rfl⟩, ?_,by simp⟩
      refine ⟨⟨h0,h1,h2,h3,by simp,?_,?_⟩,h4⟩
      · intro j hj k hk
        dsimp only
        by_cases hij : j = i
        · subst j
          by_cases hkp : k = P
          · subst k
            simp
          · rw [Function.update_of_ne (by omega), ite_eq_right hkp]
            exact (hframe _ (Or.inr (by omega))).trans (hz _ (by omega))
        · have hj' : j < i := by omega
          have hprev := Nat.mul_le_mul_right L hj'
          rw [Nat.succ_mul] at hprev
          rw [Function.update_of_ne (by omega)]
          exact hdone j hj' k hk
      · intro a ha
        dsimp only
        rw [Nat.succ_mul] at ha
        rw [Function.update_of_ne (by omega)]
        exact hframe a (ha.imp_right (by omega)))
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st hout
    cases o with
    | returned _ => exact hout
    | normal =>
      obtain ⟨h0,h1,h2,_,_,hnum,hframe⟩ := hout
      exact ⟨⟨h0,h1,h2⟩, fun i hi => unitWeight_value hP (hnum i hi),
        fun a ha => hframe a (Or.inl ha),
        fun a ha => (hframe a (Or.inr ha)).trans (hz a (by
          change heap + m * L ≤ a at ha
          omega))⟩
  · intro _ _
    simp [Expr.size_const, Expr.size_reg, Nat.mul_comm]

/-- Initialize unit blocks and return the end of their allocation. -/
def unitWeightsBody : Stmt :=
  .seq unitWeightsLoop (.ret (.bin .add (.reg 0) (.bin .mul (.reg 2) (.reg 1))))

/-- The unit block pass is deterministic. -/
theorem unitWeightsBody_noRand : unitWeightsBody.NoRand := by
  simp [unitWeightsBody, unitWeightsLoop, forRange, forUp, Stmt.NoRand]

/-- The callable unit block pass sets every compact initial weight to one. -/
def unitWeightsContract (w : ℕ) : Contract where
  pre args mem := ∃ heap L m P, args = [heap,L,m,P] ∧
    1 < 2^w ∧ P + 1 < L ∧ ZeroFrom mem heap ∧ heap + m*L < 2^w
  post args mem ret out := ∃ heap L m P, args = [heap,L,m,P] ∧ ret = heap + m*L ∧
    (∀ i < m, Valid out (heap+i*L) 1 L ∧ fixVal out (heap+i*L) 1 L P = 1) ∧
    (∀ a < heap, out a = mem a) ∧ ZeroFrom out ret
  cost args _ := 18 * args.getD 2 0 + 14

/-- The installed initializer meets its unit-weight table contract. -/
theorem unitWeights_meetsContract {w entry : ℕ} {p : Program}
    (hp : p.procs[entry]? = some unitWeightsBody) :
    MeetsContract w p entry (unitWeightsContract w) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨heap,L,m,P,rfl,hw,hP,hz,hroom⟩ := hpre
  have hm := hwords m (by simp)
  have hL := hwords L (by simp)
  have hloop := unitWeightsLoop_triple p mem pos heap L m P hw hm hL hP hz hroom
  obtain ⟨o, mid, cost, hr, hpost, hc⟩ := hloop _ ω rfl
  cases o with
  | returned => exact False.elim hpost
  | normal =>
    obtain ⟨⟨h0,h1,h2⟩, hpost⟩ := hpost
    have hret : Runs w p ω (.ret (.bin .add (.reg 0) (.bin .mul (.reg 2) (.reg 1))))
        mid (.returned (heap + m*L)) mid 6 := by
      apply runs_ret_iff.mpr
      have hmL : m*L < 2^w := by omega
      have hheap : heap < 2^w := by omega
      exact ⟨_, by eval_expr, rfl, rfl, rfl⟩
    change cost ≤ 18*m+7 at hc
    refine ⟨.returned (heap+m*L),mid,cost+7,
      runs_seq_iff.mpr (Or.inr ⟨mid,cost,6,hr,hret,rfl⟩),
      ⟨heap,L,m,P,rfl,rfl,hpost⟩,?_⟩
    change cost+7 ≤ 18*m+14
    omega

/-- Write a unit bit for each live name listed in the compact input.
Registers zero through four hold the table base, limb count, live
count, fractional precision, and name-array base. -/
def namedUnitWeightsLoop : Stmt :=
  forRange 5 (.const 0) (.reg 2)
    (.store (.bin .add
      (.bin .add (.reg 0) (.bin .mul (.load (.bin .add (.reg 4) (.reg 5))) (.reg 1)))
      (.reg 3)) (.const 1))

/-- Initialize the named blocks in time proportional to the live
edge count. The capacity reserves addresses without scanning the gaps. -/
theorem namedUnitWeightsLoop_triple {w : ℕ} {p : Program} (mem : ℕ → ℕ)
    (pos heap L m P names cap : ℕ) (name : ℕ → ℕ)
    (hw : 1 < 2^w) (hm : m < 2^w) (_hL : L < 2^w) (hP : P + 1 < L)
    (hsrc : names + m ≤ heap) (hz : ZeroFrom mem heap) (hroom : heap + cap * L < 2^w)
    (hnames : ∀ i < m, mem (names+i) = name i ∧ name i < cap ∧ name i < 2^w) :
    Triple w p (fun st => st = startState [heap,L,m,P,names] mem pos) namedUnitWeightsLoop
      (normalPost fun st =>
        (∀ i < m, Valid st.mem (heap + name i * L) 1 L ∧
          fixVal st.mem (heap + name i * L) 1 L P = 1) ∧
        (∀ a < heap, st.mem a = mem a) ∧ ZeroFrom st.mem (heap + cap * L))
      (fun _ => 21 * m + 7) := by
  classical
  let loc := fun j => heap + name j * L + P
  let Inv := fun i (st : State) =>
    st.regs 0 = heap ∧ st.regs 1 = L ∧ st.regs 2 = m ∧ st.regs 3 = P ∧
    st.regs 4 = names ∧ st.regs 5 = i ∧
    ∀ a, st.mem a = if ∃ j < i, loc j = a then 1 else mem a
  have hloc (i : ℕ) (hi : i < m) :
      heap ≤ loc i ∧ loc i < heap + cap * L := by
    have hc := Nat.mul_le_mul_right L (hnames i hi).2.1
    rw [Nat.succ_mul] at hc
    dsimp [loc]
    omega
  have loop := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 2)
    (body := .store (.bin .add
      (.bin .add (.reg 0) (.bin .mul (.load (.bin .add (.reg 4) (.reg 5))) (.reg 1)))
      (.reg 3)) (.const 1))
    (Inv := Inv) (P := fun st => st = startState [heap,L,m,P,names] mem pos)
    12 0 m (Nat.zero_le _) hw (fun _ => hm)
    (fun st hs => by subst st; exact ⟨by eval_expr, by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.1)
    (fun i st _ _ h => by
      have hreg := h.2.2.1
      eval_expr)
    (fun i _ hi => by
      intro st ω ⟨h0,h1,h2,h3,h4,h5,hmem⟩
      obtain ⟨hread, _, hname⟩ := hnames i hi
      have ha : names+i < heap := by omega
      have hread' : st.mem (names+i) = name i := by
        rw [hmem, ite_eq_right]
        · exact hread
        · rintro ⟨j,hj,he⟩
          have h := (hloc j (hj.trans hi)).1
          omega
      have hadd := hloc i hi
      have haddr : heap + name i * L + P < 2^w := hadd.2.trans hroom
      have hoff : heap + name i * L < 2^w := by omega
      have hprod : name i * L < 2^w := by omega
      have hai : names+i < 2^w := by omega
      refine ⟨.normal, {st with mem := Function.update st.mem (loc i) 1}, 12,
        runs_store_iff.mpr ⟨loc i,1,by dsimp [loc]; eval_expr,by eval_expr,rfl,rfl,rfl⟩, ?_,le_rfl⟩
      refine ⟨⟨h0,h1,h2,h3,h4,by simp,?_⟩,h5⟩
      intro a
      change Function.update st.mem (loc i) 1 a = _
      by_cases he : loc i = a
      · rw [← he, Function.update_self, ite_eq_left ⟨i,Nat.lt_succ_self _,rfl⟩]
      · rw [Function.update_of_ne (Ne.symm he), hmem]
        have heq : (∃ j < i+1, loc j = a) ↔ ∃ j < i, loc j = a := by
          constructor
          · rintro ⟨j,hj,hjloc⟩
            refine ⟨j, ?_, hjloc⟩
            by_contra hn
            have : j = i := by omega
            exact he (this ▸ hjloc)
          · rintro ⟨j,hj,hjloc⟩
            exact ⟨j, by omega, hjloc⟩
        simp only [heq])
  refine loop.conseq (fun _ h => h) ?_ ?_
  · intro o st h
    cases o with
    | returned => exact h
    | normal =>
      have hmem := h.2.2.2.2.2.2
      refine ⟨?_, ?_, ?_⟩
      · intro i hi
        apply unitWeight_value hP
        intro k hk
        rw [hmem]
        by_cases he : k = P
        · subst k
          rw [ite_eq_left ⟨i,hi,rfl⟩, ite_eq_left rfl]
        · rw [ite_eq_right he, ite_eq_right]
          · exact hz _ (by omega)
          · rintro ⟨j,_,hj⟩
            have he' : name j * L + P = name i * L + k := by
              dsimp [loc] at hj
              omega
            have hb := congrArg (· % L) he'
            simp [Nat.mod_eq_of_lt hk, Nat.mod_eq_of_lt (show P < L by omega)] at hb
            exact he hb.symm
      · intro a ha
        rw [hmem, ite_eq_right]
        rintro ⟨j,hj,he⟩
        have := (hloc j hj).1
        omega
      · intro a ha
        rw [hmem, ite_eq_right]
        · exact hz _ (by omega)
        · rintro ⟨j,hj,he⟩
          have := (hloc j hj).2
          omega
  · intro _ _
    simp [Expr.size_const, Expr.size_reg, Nat.mul_comm]

/-- On an array of live edge names, the initializer supplies the shared
unit denominator layout for the corresponding branch. -/
theorem namedUnitDenominator_triple {w : ℕ} {p : Program} (G : MGraph)
    (mem : ℕ → ℕ) (pos heap L P names cap : ℕ)
    (hw : 1 < 2^w) (hm : G.m < 2^w) (hL : L < 2^w) (hP : P + 1 < L)
    (hsrc : names + G.m ≤ heap) (hz : ZeroFrom mem heap)
    (hroom : heap + cap * L < 2^w) (hcap : cap ≤ 2^w)
    (hname : ∀ i < G.m, mem (names+i) = edgeName G i)
    (hbound : ∀ e ∈ G.E, e < cap) :
    Triple w p (fun st => st = startState [heap,L,G.m,P,names] mem pos) namedUnitWeightsLoop
      (normalPost fun st => MinRatio.EdgeValuesAt st.mem heap 1 L P G.E (fun _ => 1) ∧
        (∀ a < heap, st.mem a = mem a) ∧ ZeroFrom st.mem (heap + cap * L))
      (fun _ => 21 * G.m + 7) := by
  have hnames (i : ℕ) (hi : i < G.m) :
      mem (names+i) = edgeName G i ∧ edgeName G i < cap ∧ edgeName G i < 2^w := by
    have hb := hbound _ (edgeName_mem hi)
    exact ⟨hname i hi, hb, hb.trans_le hcap⟩
  refine (namedUnitWeightsLoop_triple mem pos heap L G.m P names cap (edgeName G)
    hw hm hL hP hsrc hz hroom hnames).conseq (fun _ h => h) ?_ (fun _ _ => le_rfl)
  intro o st h
  cases o with
  | returned => exact h
  | normal =>
    refine ⟨?_, h.2⟩
    intro e he
    obtain ⟨hi, hname⟩ := edgeIndex_live he
    exact hname ▸ h.1 (edgeIndex G e) hi

/-- The installed denominator pass writes units at the listed names. -/
def namedUnitDenominatorBody : Stmt := .seq namedUnitWeightsLoop (.ret (.const 0))

/-- The denominator pass contains no random instruction. -/
theorem namedUnitDenominatorBody_noRand : namedUnitDenominatorBody.NoRand := by
  simp [namedUnitDenominatorBody, namedUnitWeightsLoop, forRange, forUp, Stmt.NoRand]

/-- Contract for initializing a branch's named denominator values. -/
def namedUnitDenominatorContract (w : ℕ) (G : MGraph) (cap : ℕ) : Contract where
  pre args mem := ∃ heap L P names, args = [heap,L,G.m,P,names] ∧
    1 < 2^w ∧ P + 1 < L ∧ names + G.m ≤ heap ∧ ZeroFrom mem heap ∧
    heap + cap * L < 2^w ∧ cap ≤ 2^w ∧
    (∀ i < G.m, mem (names+i) = edgeName G i) ∧ (∀ e ∈ G.E, e < cap)
  post args mem ret out := ∃ heap L P names, args = [heap,L,G.m,P,names] ∧ ret = 0 ∧
    MinRatio.EdgeValuesAt out heap 1 L P G.E (fun _ => 1) ∧
    (∀ a < heap, out a = mem a) ∧ ZeroFrom out (heap + cap * L)
  cost _ _ := 21 * G.m + 10

/-- The named denominator procedure meets its contract at the
installed index for every tape and starting memory. -/
theorem namedUnitDenominator_meetsContract {w entry : ℕ} {p : Program}
    (G : MGraph) (cap : ℕ) (hp : p.procs[entry]? = some namedUnitDenominatorBody) :
    MeetsContract w p entry (namedUnitDenominatorContract w G cap) := by
  apply meetsContract_of_runs hp
  intro args mem pos ω hwords hpre
  obtain ⟨heap,L,P,names,rfl,hw,hP,hsrc,hz,hroom,hcap,hname,hbound⟩ := hpre
  have hm := hwords G.m (by simp)
  have hL := hwords L (by simp)
  have ht := namedUnitDenominator_triple (p := p) G mem pos heap L P names cap
    hw hm hL hP hsrc hz hroom hcap hname hbound
  apply runs_start_le
  unfold namedUnitDenominatorBody
  refine runs_seq_triple_le ht rfl ?_
  intro st hpost
  refine runs_ret_le (v := 0) (by eval_expr) ⟨heap,L,P,names,rfl,rfl,hpost⟩ ?_
  simp [namedUnitDenominatorContract, Expr.size]

/-- Each initial host weight is a copy of the same fixed-point unit.
The destination uses the same runtime stride as later weight rounds. -/
def stridedUnitWeightArgs : List Expr :=
  [.reg 0,.bin .add (.reg 1) (.bin .mul (.reg 5) (.reg 3)),.reg 2]

/-- Fill the live initial weight slots, leaving the reserved gaps alone.
Arguments are the unit pointer, destination, limb count, stride, and count. -/
def stridedUnitWeightLoop (copy : ℕ) : Stmt :=
  forRange 5 (.const 0) (.reg 4) (.call 6 copy stridedUnitWeightArgs)

/-- One strided copy receives the common unit block and the exact
destination address for this edge. -/
theorem stridedUnitWeightArgs_eval {w : ℕ} {st : State}
    (unit dst L stride i : ℕ)
    (hu : st.regs 0 = unit) (hd : st.regs 1 = dst) (hL : st.regs 2 = L)
    (hs : st.regs 3 = stride) (hi : st.regs 5 = i)
    (hf : dst+i*stride < 2^w) :
    evalArgs w st stridedUnitWeightArgs = some [unit,dst+i*stride,L] := by
  have hm : i*stride < 2^w := (Nat.le_add_left _ _).trans_lt hf
  simp only [stridedUnitWeightArgs,evalArgs,Expr.eval,BinOp.eval,hu,hd,hL,hs,hi,hm,hf,ite_eq_left]

/-- The initial host table contains one at every live index, with the
same stride and fixed-point grid used by the update rounds. -/
theorem stridedUnitWeightLoop_triple {w copy h P : ℕ} {p : Program}
    (hc : MeetsContract w p copy (copyWordsContract w))
    (mem : ℕ → ℕ) (pos unit dst L stride m : ℕ)
    (hw : 1 < 2^w) (hm : m < 2^w) (hL : L < 2^w) (hstride : L ≤ stride)
    (hsrc : unit+L ≤ dst) (hroom : dst+m*stride < 2^w)
    (hv : Valid mem unit h L) (hone : fixVal mem unit h L P = 1) :
    Triple w p (fun st => st = startState [unit,dst,L,stride,m] mem pos)
      (stridedUnitWeightLoop copy)
      (normalPost fun st =>
        (∀ i < m, Valid st.mem (dst+i*stride) h L ∧ fixVal st.mem (dst+i*stride) h L P = 1) ∧
        ∀ a, a < dst ∨ dst+m*stride ≤ a → st.mem a = mem a)
      (fun _ => (17*L+27)*m+7) := by
  let Inv := fun i (st : State) =>
    st.regs 0 = unit ∧ st.regs 1 = dst ∧ st.regs 2 = L ∧ st.regs 3 = stride ∧
    st.regs 4 = m ∧ st.regs 5 = i ∧
    (∀ j < i, ∀ k < L, st.mem (dst+j*stride+k) = mem (unit+k)) ∧
    ∀ a, a < dst ∨ dst+i*stride ≤ a → st.mem a = mem a
  have step := Triple.forRange_const (p := p) (r := 5) (lo := .const 0) (hi := .reg 4)
    (body := .call 6 copy stridedUnitWeightArgs)
    (Inv := Inv) (P := fun st => st = startState [unit,dst,L,stride,m] mem pos)
    (17*L+18) 0 m (Nat.zero_le _) hw (fun _ => hm)
    (fun st hs => by subst st; exact ⟨by eval_expr,by simp [Inv,startState]⟩)
    (fun _ _ _ _ h => h.2.2.2.2.2.1)
    (fun _ st _ _ h => by have hr := h.2.2.2.2.1; eval_expr)
    (fun i _ hi st ω ⟨h0,h1,h2,h3,h4,h5,hprev,hframe⟩ => by
      let base := dst+i*stride
      have hi' := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hi)
      rw [Nat.succ_mul] at hi'
      have hfit : base+L < 2^w := by dsimp [base]; omega
      have hargs := stridedUnitWeightArgs_eval unit dst L stride i h0 h1 h2 h3 h5
        ((Nat.le_add_right _ _).trans_lt hfit)
      have hwords : ∀ a ∈ [unit,base,L], a < 2^w := by
        intro a ha
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
        rcases ha with rfl | rfl | rfl <;> dsimp [base] at * <;> omega
      obtain ⟨out,cost,ret,hr,hpost,_,hregs,hcost⟩ :=
        runs_call_of_meetsContract (r := 6) hc hargs hwords
          ⟨unit,base,L,rfl,hw,by dsimp [base] at *; omega,hfit.le,
            Or.inr (hsrc.trans (Nat.le_add_right _ _))⟩ ω
      obtain ⟨s,d,l,he,_,hcopy,hout⟩ := hpost
      simp only [List.cons.injEq,and_true] at he
      obtain ⟨rfl,rfl,rfl⟩ := he
      refine ⟨.normal,out,cost,hr,⟨⟨(hregs _ (by decide)).trans h0,
        (hregs _ (by decide)).trans h1,(hregs _ (by decide)).trans h2,
        (hregs _ (by decide)).trans h3,(hregs _ (by decide)).trans h4,by simp,?_,?_⟩,
        (hregs _ (by decide)).trans h5⟩,?_⟩
      · intro j hj k hk
        by_cases heq : j = i
        · subst j
          exact (hcopy k hk).trans (hframe _ (Or.inl (by omega)))
        · have hj' : j < i := by omega
          have hjMul := Nat.mul_le_mul_right stride (Nat.succ_le_of_lt hj')
          rw [Nat.succ_mul] at hjMul
          exact (hout _ (Or.inl (by omega))).trans (hprev j hj' k hk)
      · intro a ha
        have hnext : dst+(i+1)*stride = base+stride := by simp [base,Nat.succ_mul,Nat.add_assoc]
        rw [hnext] at ha
        exact (hout a (by dsimp [base] at *; omega)).trans (hframe a (by dsimp [base] at *; omega))
      · change cost ≤ 7+(17*L+10)+1 at hcost
        change cost ≤ 17*L+18
        omega)
  refine step.conseq (fun _ h => h) ?_ ?_
  · intro o st hpost
    cases o with
    | returned => exact hpost
    | normal =>
      obtain ⟨_,_,_,_,_,_,hblocks,hframe⟩ := hpost
      refine ⟨?_,hframe⟩
      intro i hi
      have hm' := hblocks i hi
      refine ⟨fun k hk => (hm' k hk).trans_lt (hv k hk),?_⟩
      unfold fixVal at *
      rw [intVal_congr hm']
      exact hone
  · intro st _
    simp only [Nat.sub_zero,Expr.size]
    rw [Nat.mul_comm m]

/-- Fill the initial weights and return zero. -/
def stridedUnitWeightBody (copy : ℕ) : Stmt :=
  .seq (stridedUnitWeightLoop copy) (.ret (.const 0))

/-- The initializer receives the runtime width and stride. All
addresses below and above the reserved table retain their contents. -/
def stridedUnitWeightContract (w h P : ℕ) : Contract where
  pre args mem := ∃ unit dst L stride m, args = [unit,dst,L,stride,m] ∧
    1 < 2^w ∧ L ≤ stride ∧ unit+L ≤ dst ∧ dst+m*stride < 2^w ∧
    Valid mem unit h L ∧ fixVal mem unit h L P = 1
  post args mem ret out := ∃ unit dst L stride m, args = [unit,dst,L,stride,m] ∧ ret = 0 ∧
    (∀ i < m, Valid out (dst+i*stride) h L ∧ fixVal out (dst+i*stride) h L P = 1) ∧
    ∀ a, a < dst ∨ dst+m*stride ≤ a → out a = mem a
  cost args _ := (17*args.getD 2 0+27)*args.getD 4 0+10

/-- The installed strided initializer meets its ordinary call contract. -/
theorem stridedUnitWeight_meetsContract {w h P entry copy : ℕ} {p : Program}
    (he : p.procs[entry]? = some (stridedUnitWeightBody copy))
    (hc : MeetsContract w p copy (copyWordsContract w)) :
    MeetsContract w p entry (stridedUnitWeightContract w h P) := by
  apply meetsContract_of_runs he
  intro args mem pos ω hwords hpre
  obtain ⟨unit,dst,L,stride,m,rfl,hw,hstride,hsrc,hroom,hv,hu⟩ := hpre
  apply runs_start_le
  unfold stridedUnitWeightBody
  refine runs_seq_triple_le (stridedUnitWeightLoop_triple hc mem pos unit dst L stride m
    hw (hwords _ (by simp)) (hwords _ (by simp)) hstride hsrc hroom hv hu) rfl ?_
  intro out ⟨hvalues,hframe⟩
  refine runs_ret_le (v := 0) (by eval_expr)
    ⟨unit,dst,L,stride,m,rfl,rfl,hvalues,hframe⟩ ?_
  change 0+((17*L+27)*m+7)+1+2 ≤ (17*L+27)*m+10
  omega

end MinCostFlow.LastLevelProgram
