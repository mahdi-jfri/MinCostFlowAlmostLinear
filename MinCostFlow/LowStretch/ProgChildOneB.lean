module

public import MinCostFlow.LowStretch.ProgChildOneA
public import MinCostFlow.LowStretch.ProgChildHw
public import MinCostFlow.LowStretch.ProgChildPairs
public import MinCostFlow.LowStretch.ProgChildNodes
public import MinCostFlow.LowStretch.ProgChildSize

/-!
# One child: the calls before the radius

After the loads, `oneP` calls `hwWalkP`, `pcP` and `ncP`, writes the record block, and calls
`smP`. This file follows these steps (`oneB_runs`). The preconditions of the calls are taken as
hypotheses here, stated for any memory that the earlier calls may leave; the next files prove them
from the invariant of the loop. The result lists what each call has done, so that the next files
can read off the record of the child.
-/

@[expose] public section

namespace MinCostFlow.LowStretch

open WordRAM

theorem evalArgs_rgs {w : ℕ} {st : State} :
    ∀ l : List ℕ, evalArgs w st (rgs l) = some (l.map st.regs)
  | [] => rfl
  | r :: l => by
      rw [show rgs (r :: l) = .reg r :: rgs l from rfl, List.map_cons]
      simp [evalArgs, Expr.eval_reg, evalArgs_rgs l]

theorem argsSize_rgs : ∀ l : List ℕ, argsSize (rgs l) = l.length
  | [] => rfl
  | r :: l => by
      rw [show rgs (r :: l) = .reg r :: rgs l from rfl, argsSize, argsSize_rgs l]
      simp [Expr.size]; omega

theorem runs_exists_mono {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {Q : Outcome → State → Prop} {A A' T : ℕ}
    (h : ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ A + c ≤ T) (hA : A' ≤ A) :
    ∃ o st' c, Runs w p ω s st o st' c ∧ Q o st' ∧ A' + c ≤ T := by
  obtain ⟨o, st', c, h1, h2, h3⟩ := h
  exact ⟨o, st', c, h1, h2, by omega⟩

/-- A call whose arguments are registers. -/
theorem runs_seq_callR_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {l : List ℕ}
    {C : Contract} {s : Stmt} {st : State} {vs : List ℕ} {k T : ℕ} {Q : Outcome → State → Prop}
    (hf : MeetsContract w p f C) (hvs : l.map st.regs = vs) (hwords : ∀ v ∈ vs, v < 2 ^ w)
    (hpre : C.pre vs st.mem)
    (hrest : ∀ v mem' pos', C.post vs st.mem v mem' →
      ∃ o st' c, Runs w p ω s { mem := mem', regs := Function.update st.regs r v, pos := pos' }
        o st' c ∧ Q o st' ∧ (k + l.length + C.cost vs st.mem + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f (rgs l)) s) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_call_le hf (by rw [evalArgs_rgs, hvs]) hwords hpre
    (fun v m q h => by rw [argsSize_rgs]; exact hrest v m q h)

namespace OneV

variable (V : OneV)

/-- The numbers of the calls of `oneP`, for a highway of `ℓ` entries. -/
def hwE (M : ℕ → ℕ) : HWE := ⟨V.u0, V.v0, V.rg, V.PAR, V.PP, V.PF, V.PA, V.PB, V.HM, V.H, M⟩

def SA (ℓ : ℕ) : ℕ := V.H + 4 * ℓ
def NA (ℓ : ℕ) : ℕ := V.SA ℓ + 2 * V.cnt
def OUT (ℓ : ℕ) : ℕ := V.NA ℓ + V.sN

def pcE (ℓ : ℕ) (M : ℕ → ℕ) : PCE :=
  ⟨V.cnt, V.SRCK, V.ACT, V.IN, V.LAB, V.LOC, V.HM, V.PP, 1, V.SA ℓ, M⟩

def ncE (ℓ : ℕ) (M : ℕ → ℕ) : NCE := ⟨V.sN, V.SRCN, V.NAp, V.HEAD, V.LOC, V.NA ℓ, M⟩

def smE (ℓ : ℕ) (M : ℕ → ℕ) : SME := ⟨V.sN, V.NA ℓ, V.KSZ, V.KMW, V.OUT ℓ, M⟩

/-- The record block that `oneP` writes. -/
def blk (ℓ : ℕ) : List ℕ := [V.sN, V.cnt, V.SA ℓ, V.lθ, V.NA ℓ, V.cc, V.ct, ℓ, V.H]

/-- The memory after the record block is written on `M`. -/
def putBlk (ℓ : ℕ) (M : ℕ → ℕ) (a : ℕ) : ℕ :=
  if V.BK ≤ a ∧ a < V.BK + 9 then (V.blk ℓ).getD (a - V.BK) 0 else M a

/-- What the calls need: the preconditions for any memory the earlier calls may leave, and the
word bounds. -/
structure CallsOk (w : ℕ) (V : OneV) (M : ℕ → ℕ) (s ℓ : ℕ) : Prop where
  hw : (V.hwE M).Ok w s ℓ
  pc : ∀ M2, (V.hwE M).Done ℓ M2 → (V.pcE ℓ M2).Ok w
  nc : ∀ M2 M3, (V.hwE M).Done ℓ M2 → (V.pcE ℓ M2).Done V.cnt M3 → ∃ N, (V.ncE ℓ M3).Ok w N
  sm : ∀ M2 M3 M4, (V.hwE M).Done ℓ M2 → (V.pcE ℓ M2).Done V.cnt M3 →
    (V.ncE ℓ M3).Done V.sN M4 → (V.smE ℓ (V.putBlk ℓ M4)).Ok w
  words : ∀ r < 39, V.vals.getD r 0 < 2 ^ w
  room : V.OUT ℓ + 2 < 2 ^ w
  bk : V.BK + 9 < 2 ^ w

end OneV

namespace OneV

variable {V : OneV}

theorem Regs.of_eq {st st' : State} (h : V.Regs st)
    (he : ∀ r, (r < 39 ∨ r = 42 ∨ r = 43 ∨ r = 44) → st'.regs r = st.regs r) : V.Regs st' :=
  ⟨fun r hr => (he r (Or.inl hr)).trans (h.1 r hr), (he 42 (by omega)).trans h.2.1,
    (he 43 (by omega)).trans h.2.2.1, (he 44 (by omega)).trans h.2.2.2⟩

theorem putBlk_eq (ℓ : ℕ) (M : ℕ → ℕ) :
    Function.update (Function.update (Function.update (Function.update (Function.update
      (Function.update (Function.update (Function.update (Function.update M V.BK V.sN)
      (V.BK + 1) V.cnt) (V.BK + 2) (V.SA ℓ)) (V.BK + 3) V.lθ) (V.BK + 4) (V.NA ℓ))
      (V.BK + 5) V.cc) (V.BK + 6) V.ct) (V.BK + 7) ℓ) (V.BK + 8) V.H = V.putBlk ℓ M := by
  funext a
  simp only [putBlk, Function.update_apply]
  split_ifs <;> first | omega | (subst_vars; simp [blk]) | rfl

end OneV

set_option maxHeartbeats 1000000 in
/-- **The calls before the radius.** From the loads to the test `|X| < 2`: the highway, the stored
pairs, the nodes, the record block and the two sums. -/
theorem oneB_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {I : CIdx} {V : OneV} {M : ℕ → ℕ}
    {s ℓ : ℕ} (fhw : MeetsContract w p I.hw (hwC w)) (fpc : MeetsContract w p I.pc (pcC w))
    (fnc : MeetsContract w p I.nc (ncC w)) (fsm : MeetsContract w p I.sm (smC w))
    (hC : V.CallsOk w M s ℓ) {st : State} (hR : V.Regs st) (hM : st.mem = M)
    {Q : Outcome → State → Prop} {T : ℕ}
    (hrest : ∀ M2 M3 M4 (st' : State), (V.hwE M).Done ℓ M2 → (V.pcE ℓ M2).Done V.cnt M3 →
      (V.ncE ℓ M3).Done V.sN M4 →
      st'.mem = Function.update (Function.update (V.putBlk ℓ M4) (V.OUT ℓ)
        ((V.smE ℓ (V.putBlk ℓ M4)).sum V.sN)) (V.OUT ℓ + 1) ((V.smE ℓ (V.putBlk ℓ M4)).mx V.sN) →
      V.Regs st' → st'.regs 39 = ℓ → st'.regs 40 = V.SA ℓ → st'.regs 45 = V.NA ℓ →
      st'.regs 46 = V.OUT ℓ → st'.regs 47 = st'.mem (V.OUT ℓ) →
      st'.regs 48 = st'.mem (V.OUT ℓ + 1) → st'.regs 49 = V.OUT ℓ + 2 →
      ∃ o st'' c, Runs w p ω (.cond (.bin .lt (.reg 47) (.const 2)) (.ret (.reg 49)) (oneD I))
        st' o st'' c ∧ Q o st'' ∧ 160 * ℓ + 200 * V.cnt + 110 * V.sN + 1000 + c ≤ T) :
    ∃ o st' c, Runs w p ω (oneB I) st o st' c ∧ Q o st' ∧ c ≤ T := by
  have W := hC.words
  have room := hC.room
  have bk := hC.bk
  have hSA : V.SA ℓ = V.H + 4 * ℓ := rfl
  have hNA : V.NA ℓ = V.SA ℓ + 2 * V.cnt := rfl
  have hOUT : V.OUT ℓ = V.NA ℓ + V.sN := rfl
  have wH : V.H < 2 ^ w := W 5 (by norm_num)
  unfold oneB
  refine runs_start_le ?_
  -- the highway
  refine runs_seq_callR_le (vs := (V.hwE M).args) fhw ?_ ?_ ⟨V.hwE M, s, ℓ, rfl, hM.symm, hC.hw⟩ ?_
  · simp only [List.map_cons, List.map_nil, OneV.hwE, HWE.args, List.cons.injEq, and_true]
    exact ⟨hR.1 32 (by norm_num), hR.1 33 (by norm_num), hR.1 34 (by norm_num),
      hR.1 21 (by norm_num), hR.1 22 (by norm_num), hR.1 23 (by norm_num), hR.1 24 (by norm_num),
      hR.1 25 (by norm_num), hR.1 10 (by norm_num), hR.1 5 (by norm_num)⟩
  · simp only [OneV.hwE, HWE.args, List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [W 32 (by norm_num), W 33 (by norm_num), W 34 (by norm_num), W 21 (by norm_num),
      W 22 (by norm_num), W 23 (by norm_num), W 24 (by norm_num), W 25 (by norm_num),
      W 10 (by norm_num), W 5 (by norm_num)]
  intro v1 M2 q1 hp1
  obtain ⟨hv1, hd1⟩ := hp1 (V.hwE M) s ℓ rfl hM.symm hC.hw
  have hv1' : ℓ = v1 := hv1.symm
  subst hv1'
  have hc1 : (hwC w).cost (V.hwE M).args st.mem = 160 * ℓ + 20 := by
    show 160 * hwLenOf _ _ + 20 = _
    rw [hM]; exact congrArg (fun x => 160 * x + 20) hC.hw.len
  rw [hc1]
  have R1 := hR.upd (r := 39) (by norm_num) (by norm_num) (by norm_num) (by norm_num) ℓ M2 q1
  -- the address of the stored pairs
  refine runs_seq_assign_le (v := V.SA ℓ) (Expr.eval_add
    (Expr.eval_reg_of_eq (R1.1 5 (by norm_num)))
    (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (by simp))
      (by omega)) (by omega)) ?_
  have R2 := R1.upd (r := 40) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (V.SA ℓ)
    M2 q1
  -- the stored pairs
  refine runs_seq_callR_le (vs := (V.pcE ℓ M2).args) fpc ?_ ?_ ⟨V.pcE ℓ M2, rfl, rfl,
    hC.pc M2 hd1⟩ ?_
  · simp only [List.map_cons, List.map_nil, OneV.pcE, PCE.args, List.cons.injEq, and_true]
    refine ⟨R2.1 36 (by norm_num), R2.1 35 (by norm_num), R2.1 26 (by norm_num),
      R2.1 11 (by norm_num), R2.1 14 (by norm_num), R2.1 15 (by norm_num), R2.1 10 (by norm_num),
      R2.1 22 (by norm_num), R2.2.1, by simp⟩
  · simp only [OneV.pcE, PCE.args, List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [W 36 (by norm_num), W 35 (by norm_num), W 26 (by norm_num), W 11 (by norm_num),
      W 14 (by norm_num), W 15 (by norm_num), W 10 (by norm_num), W 22 (by norm_num),
      by omega, by omega]
  intro v2 M3 q2 hp2
  have hd2 := hp2 (V.pcE ℓ M2) rfl rfl
  have R3 := R2.upd (r := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num) v2 M3 q2
  have hc2 : (pcC w).cost (V.pcE ℓ M2).args M2 = 200 * (V.cnt + 1) := rfl
  rw [hc2]
  -- the address of the nodes
  refine runs_seq_assign_le (v := V.NA ℓ) (Expr.eval_add (Expr.eval_reg_of_eq (by simp))
    (Expr.eval_mul (Expr.eval_const (by omega)) (Expr.eval_reg_of_eq (R3.1 36 (by norm_num)))
      (by have := W 36 (by norm_num); simp only [OneV.vals] at this ⊢; omega)) (by omega)) ?_
  have R4 := R3.upd (r := 45) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (V.NA ℓ)
    M3 q2
  -- the nodes
  obtain ⟨N, hN⟩ := hC.nc M2 M3 hd1 hd2
  refine runs_seq_callR_le (vs := (V.ncE ℓ M3).args) fnc ?_ ?_ ⟨V.ncE ℓ M3, N, rfl, rfl, hN⟩ ?_
  · simp only [List.map_cons, List.map_nil, OneV.ncE, NCE.args, List.cons.injEq, and_true]
    refine ⟨R4.1 38 (by norm_num), R4.1 37 (by norm_num), R4.1 29 (by norm_num),
      R4.1 16 (by norm_num), R4.1 15 (by norm_num), by simp⟩
  · simp only [OneV.ncE, NCE.args, List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl | rfl)
    exacts [W 38 (by norm_num), W 37 (by norm_num), W 29 (by norm_num), W 16 (by norm_num),
      W 15 (by norm_num), by omega]
  intro v3 M4 q3 hp3
  have hd3 := hp3 (V.ncE ℓ M3) rfl rfl
  have hc3 : (ncC w).cost (V.ncE ℓ M3).args M3 = 60 * (V.sN + 1) := rfl
  rw [hc3]
  have R5 := R4.upd (r := 41) (by norm_num) (by norm_num) (by norm_num) (by norm_num) v3 M4 q3
  have e39 : (Function.update (Function.update (Function.update (Function.update
      (Function.update st.regs 39 ℓ) 40 (V.SA ℓ)) 41 v2) 45 (V.NA ℓ)) 41 v3) 39 = ℓ := by simp
  have e40 : (Function.update (Function.update (Function.update (Function.update
      (Function.update st.regs 39 ℓ) 40 (V.SA ℓ)) 41 v2) 45 (V.NA ℓ)) 41 v3) 40 = V.SA ℓ := by
    simp
  have e45 : (Function.update (Function.update (Function.update (Function.update
      (Function.update st.regs 39 ℓ) 40 (V.SA ℓ)) 41 v2) 45 (V.NA ℓ)) 41 v3) 45 = V.NA ℓ := by
    simp
  have hb : ∀ i, i < 9 → (Expr.bin .add (.reg 3) (.const i)).eval w
      { mem := M4, regs := Function.update (Function.update (Function.update (Function.update
        (Function.update st.regs 39 ℓ) 40 (V.SA ℓ)) 41 v2) 45 (V.NA ℓ)) 41 v3, pos := q3 } =
      some (V.BK + i) := fun i hi =>
    Expr.eval_add (Expr.eval_reg_of_eq (R5.1 3 (by norm_num))) (Expr.eval_const (by omega))
      (by omega)
  -- the record block
  refine runs_seq_store_le (Expr.eval_reg_of_eq (R5.1 3 (by norm_num)))
    (Expr.eval_reg_of_eq (R5.1 38 (by norm_num))) ?_
  refine runs_seq_store_le (hb 1 (by norm_num)) (Expr.eval_reg_of_eq (R5.1 36 (by norm_num))) ?_
  refine runs_seq_store_le (hb 2 (by norm_num)) (Expr.eval_reg_of_eq e40) ?_
  refine runs_seq_store_le (hb 3 (by norm_num)) (Expr.eval_reg_of_eq (R5.1 28 (by norm_num))) ?_
  refine runs_seq_store_le (hb 4 (by norm_num)) (Expr.eval_reg_of_eq e45) ?_
  refine runs_seq_store_le (hb 5 (by norm_num)) (Expr.eval_reg_of_eq (R5.1 31 (by norm_num))) ?_
  refine runs_seq_store_le (hb 6 (by norm_num)) (Expr.eval_reg_of_eq (R5.1 30 (by norm_num))) ?_
  refine runs_seq_store_le (hb 7 (by norm_num)) (Expr.eval_reg_of_eq e39) ?_
  refine runs_seq_store_le (hb 8 (by norm_num)) (Expr.eval_reg_of_eq (R5.1 5 (by norm_num))) ?_
  -- the two sums
  refine runs_seq_assign_le (v := V.OUT ℓ) (Expr.eval_add (Expr.eval_reg_of_eq e45)
    (Expr.eval_reg_of_eq (R5.1 38 (by norm_num))) (by omega)) ?_
  have e5 := OneV.putBlk_eq (V := V) ℓ M4
  refine runs_seq_callR_le (vs := (V.smE ℓ (V.putBlk ℓ M4)).args) fsm ?_ ?_
    ⟨V.smE ℓ (V.putBlk ℓ M4), rfl, e5.symm, hC.sm M2 M3 M4 hd1 hd2 hd3⟩ ?_
  · simp only [List.map_cons, List.map_nil, OneV.smE, SME.args, List.cons.injEq, and_true]
    refine ⟨R5.1 38 (by norm_num), by simp, R5.1 18 (by norm_num), R5.1 17 (by norm_num),
      by simp⟩
  · simp only [OneV.smE, SME.args, List.mem_cons, List.not_mem_nil, or_false]
    rintro v (rfl | rfl | rfl | rfl | rfl)
    exacts [W 38 (by norm_num), by omega, W 18 (by norm_num), W 17 (by norm_num), by omega]
  intro v4 M6 q4 hp4
  have hm6 := hp4 (V.smE ℓ (V.putBlk ℓ M4)) rfl e5.symm
  have hc4 : ∀ m, (smC w).cost (V.smE ℓ (V.putBlk ℓ M4)).args m = 50 * (V.sN + 1) :=
    fun _ => rfl
  rw [hc4]
  refine runs_seq_assign_le (v := M6 (V.OUT ℓ)) (Expr.eval_load_of_eq
    (Expr.eval_reg_of_eq (show _ = V.OUT ℓ by simp)) rfl) ?_
  refine runs_seq_assign_le (v := M6 (V.OUT ℓ + 1)) (Expr.eval_load_of_eq
    (Expr.eval_add (Expr.eval_reg_of_eq (show _ = V.OUT ℓ by simp)) (Expr.eval_const (by omega))
      (by omega)) rfl) ?_
  refine runs_seq_assign_le (v := V.OUT ℓ + 2) (Expr.eval_add
    (Expr.eval_reg_of_eq (show _ = V.OUT ℓ by simp)) (Expr.eval_const (by omega)) (by omega)) ?_

  refine runs_exists_mono (hrest M2 M3 M4 _ hd1 hd2 hd3 (by
      rw [hm6]; exact congrArg (fun m => Function.update (Function.update m _ _) _ _) e5)
    (R5.of_eq fun r hr => by
      simp only [Function.update_apply]
      split_ifs <;> first | omega | rfl)
    (by simp) (by simp) (by simp) (by simp) (by simp) (by simp) (by simp)) ?_
  simp only [Expr.size, mulC, addR, List.length_cons, List.length_nil]
  omega

end MinCostFlow.LowStretch
