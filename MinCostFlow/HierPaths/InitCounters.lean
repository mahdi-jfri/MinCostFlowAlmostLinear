module

public import MinCostFlow.HierPaths.InitWriters

/-!
# The writer of the loss counter tables

Sections 18 and 19 of the initial block are `csrList (D + 1)` of zero tables of `numGroups j`
words, `D` the leaf depth: the data is zero, but the offsets `Σ_{i<j} numGroups i` are not.
`countersWriter` computes `D`, then for `j = 0, …, D` stores the running sum at `r6 + j` and
adds `numGroups j = 2^{min(x, j·b)}`; it keeps `t = min(x, j·b)` as
`t + min(b, x − t)`, which needs no sum `x + b`. Then it stores the last offset and returns
the end.
-/

@[expose] public section

noncomputable section

namespace MinCostFlow.HierPaths

open WordRAM MinCostFlow.Cited MinCostFlow.Spanner

/-- The total size of the zero tables before depth `j`. -/
def ngSum (x b j : ℕ) : ℕ := ((List.range j).map (numGroups x b)).sum

theorem ngSum_succ (x b j : ℕ) : ngSum x b (j + 1) = ngSum x b j + numGroups x b j := by
  simp [ngSum, List.range_succ]

/-- The loop body at counter `r13 = j`. -/
def countersBody : Stmt :=
  .seq (.store (.bin .add (.reg 6) (.reg 13)) (.reg 11))
    (.seq (.assign 11 (.bin .add (.reg 11) (.bin .shiftLeft (.const 1) (.reg 12))))
      (.assign 12 (.bin .add (.reg 12) (.bin .sub (.bin .sub (.reg 7) (.reg 12))
        (.bin .sub (.bin .sub (.reg 7) (.reg 12)) (.reg 8))))))

/-- `r7 := x`; `r8 := b`; `r9 := D`; `r10 := D + 1`; `r11 := 0`; `r12 := 0`; the loop for
`r13 < r10`; store `r11` at `r6 + r10`; return `r6 + r10 + 1 + r11`. -/
def countersWriter : Stmt :=
  .seq (.assign 7 (.load (.bin .add (.reg 4) (.const 7))))
  (.seq (.assign 8 (.load (.bin .add (.reg 4) (.const 8))))
  (.seq (.assign 9 depthExpr)
  (.seq (.assign 10 (.bin .add (.reg 9) (.const 1)))
  (.seq (.assign 11 (.const 0))
  (.seq (.assign 12 (.const 0))
  (.seq (forRange 13 (.const 0) (.reg 10) countersBody)
  (.seq (.store (.bin .add (.reg 6) (.reg 10)) (.reg 11))
    (.ret (.bin .add (.bin .add (.bin .add (.reg 6) (.reg 10)) (.const 1)) (.reg 11))))))))))

/-- The loop invariant. -/
def countersInv (c x b D : ℕ) (mem₀ : ℕ → ℕ) (j : ℕ) (st : State) : Prop :=
  st.regs 6 = c ∧ st.regs 7 = x ∧ st.regs 8 = b ∧ st.regs 10 = D + 1 ∧ st.regs 13 = j ∧
    st.regs 11 = ngSum x b j ∧ st.regs 12 = min x (j * b) ∧
    (∀ i < j, st.mem (c + i) = ngSum x b i) ∧ (∀ y, (y < c ∨ c + j ≤ y) → st.mem y = mem₀ y)

theorem ngSum_mono {x b : ℕ} {i j : ℕ} (h : i ≤ j) : ngSum x b i ≤ ngSum x b j := by
  induction h with
  | refl => exact le_rfl
  | step _ ih => rw [ngSum_succ]; omega

theorem countersBody_triple {w c x b D : ℕ} {p : Program} {mem₀ : ℕ → ℕ} {j : ℕ}
    (hj : j < D + 1) (hbound : c + (D + 1) + ngSum x b (D + 1) < 2 ^ w) (hxw : x < 2 ^ w) :
    Triple w p (countersInv c x b D mem₀ j) countersBody
      (normalPost fun st₁ =>
        countersInv c x b D mem₀ (j + 1) { st₁ with regs := Function.update st₁.regs 13 (j + 1) }
          ∧ st₁.regs 13 = j)
      (fun _ => 40) := by
  intro st ω ⟨h6, h7, h8, h10, h13, h11, h12, hmem, hfr⟩
  have hS1 := ngSum_mono (x := x) (b := b) (show j + 1 ≤ D + 1 by omega)
  rw [ngSum_succ] at hS1
  have hcj : c + j < 2 ^ w := by omega
  have hng : numGroups x b j = 1 <<< min x (j * b) := by
    simp [numGroups, Nat.shiftLeft_eq]
  have hngw : 1 <<< min x (j * b) < 2 ^ w := by rw [← hng]; omega
  have hsw : ngSum x b j + numGroups x b j < 2 ^ w := by omega
  have h1w : 1 < 2 ^ w := by
    have : 1 ≤ numGroups x b j := Nat.one_le_two_pow
    omega
  have hmin : min x (j * b) + (x - min x (j * b) - (x - min x (j * b) - b)) =
      min x ((j + 1) * b) := by
    rw [Nat.succ_mul]; omega
  refine runs_start_le ?_
  unfold countersBody
  refine runs_seq_store_le (x := c + j) (v := ngSum x b j)
    (Expr.eval_add (Expr.eval_reg_of_eq h6) (Expr.eval_reg_of_eq h13) hcj)
    (Expr.eval_reg_of_eq h11) ?_
  refine runs_seq_assign_le (v := ngSum x b j + numGroups x b j)
    (by
      rw [hng]
      exact Expr.eval_add (Expr.eval_reg_of_eq h11)
        (Expr.eval_shiftLeft (Expr.eval_const h1w) (Expr.eval_reg_of_eq h12) hngw)
        (by rw [← hng]; exact hsw)) ?_
  have hxt : x - min x (j * b) < 2 ^ w := by omega
  refine runs_assign_le (v := min x ((j + 1) * b))
    (by
      rw [← hmin]
      refine Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update, h12]))
        (Expr.eval_sub (Expr.eval_sub (Expr.eval_reg_of_eq (by simp [Function.update, h7]))
          (Expr.eval_reg_of_eq (by simp [Function.update, h12])) hxw)
          (Expr.eval_sub (Expr.eval_sub (Expr.eval_reg_of_eq (by simp [Function.update, h7]))
            (Expr.eval_reg_of_eq (by simp [Function.update, h12])) hxw)
            (Expr.eval_reg_of_eq (by simp [Function.update, h8])) hxt) hxt) ?_
      rw [hmin]; omega) ⟨⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩ ?_
  all_goals simp only [Function.update] at *
  all_goals first
    | (simp_all; done)
    | skip
  · rw [ngSum_succ]; simp_all
  · intro i hi
    by_cases hij : i = j
    · subst hij; simp
    · rw [dif_neg (by omega)]; exact hmem i (by omega)
  · intro y hy
    rw [dif_neg (by omega)]; exact hfr y (by omega)

/-- The section of the counter tables: `csrList (D + 1)` of zero tables. -/
def countersList (S : StaticData) : List ℕ :=
  csrList (leafDepth S.x S.b + 1) fun j => tabList (numGroups S.x S.b j) fun _ => 0

theorem length_countersList (S : StaticData) :
    (countersList S).length = leafDepth S.x S.b + 1 + 1 + ngSum S.x S.b (leafDepth S.x S.b + 1) := by
  rw [countersList, length_csrList, ngSum, sum_map_range]
  simp

/-- The writer of the counter tables as a `SecProc`. -/
def countersSec (S : StaticData) (f : ℕ) : SecProc where
  f := f
  l _ := countersList S
  cost _ := 60 * (leafDepth S.x S.b + 1) + 150

/-- **The writer of the counter tables meets `SecContract`.** -/
theorem countersWriter_meetsContract {w a : ℕ} {S : StaticData} {G : Graph} {p : Program}
    {f : ℕ} (hp : p.procs[f]? = some countersWriter) :
    MeetsContract w p f (SecContract w (buildInv w S a G) (countersSec S f)) := by
  refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
  obtain ⟨base, c, rfl, hbl, hI, hz, hc, hcw⟩ := hpre
  obtain ⟨h, hh, hx, hb, hh8, hxw, hb0, -⟩ := header_facts hI hw
  simp only [countersSec, length_countersList] at hcw
  set D := leafDepth S.x S.b with hD
  set st₀ := startState (base ++ [c]) mem pos with hst₀
  have h4 : st₀.regs 4 = h := by
    rw [← hh, hst₀]; simp only [startState]; rw [List.getD_append _ _ _ _ (by omega)]
  have h6 : st₀.regs 6 = c := by
    rw [hst₀]; simp only [startState]
    rw [List.getD_append_right _ _ _ _ (by omega)]; simp [hbl]
  have h1w : 1 < 2 ^ w := by omega
  have hDw : D + 1 < 2 ^ w := by omega
  refine runs_start_le ?_
  unfold countersWriter
  refine runs_seq_assign_le (v := S.x) (eval_xExpr h4 hx hh8) ?_
  refine runs_seq_assign_le (v := S.b)
    (eval_bExpr (h := h) (by simp [Function.update, h4]) hb hh8) ?_
  refine runs_seq_assign_le (v := D)
    (eval_depthExpr (h := h) (by simp [Function.update, h4]) hx hb hh8 hxw hb0) ?_
  refine runs_seq_assign_le (v := D + 1) (Expr.eval_add (Expr.eval_reg_of_eq
    (by simp [Function.update])) (Expr.eval_const h1w) hDw) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  refine runs_seq_assign_le (v := 0) (Expr.eval_const (by omega)) ?_
  have hbound : c + (D + 1) + ngSum S.x S.b (D + 1) < 2 ^ w := by omega
  refine runs_seq_triple_le (Triple.forRange_const (p := p) (r := 13) (lo := .const 0)
    (hi := .reg 10) (body := countersBody)
    (P := fun st => st.regs 6 = c ∧ st.regs 7 = S.x ∧ st.regs 8 = S.b ∧ st.regs 10 = D + 1 ∧
      st.regs 11 = 0 ∧ st.regs 12 = 0 ∧ st.mem = mem)
    (Inv := countersInv c S.x S.b D mem) 40 0 (D + 1) (Nat.zero_le _) h1w (fun _ => hDw)
    (fun st ⟨g6, g7, g8, g10, g11, g12, gm⟩ => ⟨Expr.eval_const (by omega),
      by simp [Function.update, g6], by simp [Function.update, g7],
      by simp [Function.update, g8], by simp [Function.update, g10], by simp [Function.update],
      by simp [Function.update, g11, ngSum], by simp [Function.update, g12],
      fun i hi => absurd hi (Nat.not_lt_zero _), fun y _ => by simp [gm]⟩)
    (fun _ st _ _ hi => hi.2.2.2.2.1)
    (fun _ st _ _ hi => Expr.eval_reg_of_eq hi.2.2.2.1)
    (fun j _ hj => countersBody_triple hj hbound hxw))
    ⟨by simp [Function.update, h6], by simp [Function.update], by simp [Function.update],
      by simp [Function.update], by simp [Function.update], by simp [Function.update], rfl⟩ ?_
  intro st₁ ⟨g6, g7, g8, g10, g13, g11, g12, gmem, gfr⟩
  have hcD : c + (D + 1) < 2 ^ w := by omega
  refine runs_seq_store_le (x := c + (D + 1)) (v := ngSum S.x S.b (D + 1))
    (Expr.eval_add (Expr.eval_reg_of_eq g6) (Expr.eval_reg_of_eq g10) hcD)
    (Expr.eval_reg_of_eq g11) ?_
  refine runs_ret_le (v := c + (D + 1) + 1 + ngSum S.x S.b (D + 1))
    (Expr.eval_add (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq g6)
      (Expr.eval_reg_of_eq g10) hcD) (Expr.eval_const h1w) (by omega))
      (Expr.eval_reg_of_eq g11) (by omega)) ?_ ?_
  · set mem' := Function.update st₁.mem (c + (D + 1)) (ngSum S.x S.b (D + 1)) with hmem'
    have hZ : ZeroFrom mem' (c + (D + 1) + 1) := by
      intro y hy
      rw [hmem', Function.update_of_ne (by omega), gfr y (Or.inr (by omega))]
      exact hz y (by omega)
    refine ⟨base, c, rfl, ?_, ?_, ?_, ?_⟩
    · simp only [Outcome.value, countersSec, length_countersList, ← hD]; omega
    · show ListAt mem' c (countersList S)
      refine listAt_csrList_of (listAt_csrOffsets_of fun i hi => ?_) fun i hi => ?_
      · have e : ((List.range i).map fun j =>
            (tabList (numGroups S.x S.b j) fun _ => 0).length).sum = ngSum S.x S.b i := by
          simp [ngSum]
        rw [e]
        rcases Nat.lt_or_ge i (D + 1) with hi' | hi'
        · rw [hmem', Function.update_of_ne (by omega)]; exact gmem i hi'
        · have : i = D + 1 := by omega
          subst this
          rw [hmem', Function.update_self]
      · exact listAt_of_zero hZ (by omega) (by simp [tabList])
    · intro y hy
      simp only [Outcome.value, countersSec, length_countersList, ← hD] at hy
      exact hZ y (by omega)
    · intro y hy
      show mem' y = mem y
      rw [hmem', Function.update_of_ne (by omega), gfr y (Or.inl hy)]
  · simp only [SecContract, countersSec, Expr.size, depthExpr, countersBody]
    omega

/-- Sections 18 and 19 of the initial block (the loss counters `own` and `sum`, zero at the
start) are `countersList`. -/
theorem initConcrete_sections_counters (S : StaticData) (a : ℕ) (s : PathDSAbsState) :
    (initConcrete S a s).sections.getD 18 [] = countersList S ∧
      (initConcrete S a s).sections.getD 19 [] = countersList S := by
  constructor <;>
  simp [HierConcrete.sections, HierConcrete.depth, initConcrete, StaticData.model,
    staticArrays, DelState.init, LossState.init, countersList]

theorem countersWriter_noRand : countersWriter.NoRand := by
  simp [countersWriter, countersBody, forRange, forUp, Stmt.NoRand]

/-- The counter tables as a relocatable writer. -/
def countersW (a : ℕ) : SecW a where
  body _ := countersWriter
  helpers _ := []
  l S _ _ := countersList S
  cost S _ _ := 60 * (leafDepth S.x S.b + 1) + 150
  noRand _ := ⟨countersWriter_noRand, by simp⟩
  spec w p f k hp _ S G := countersWriter_meetsContract (S := S) (G := G) hp

/-! ### A section of zeros whose length a word procedure computes -/

/-- `r7 := f(r0, …, r6)`; return `r6 + r7`. Memory from `r6` on is zero. -/
def zeroCallWriter (f : ℕ) : Stmt :=
  .seq (.call 7 f secArgs) (.ret (.bin .add (.reg 6) (.reg 7)))

/-- **A section of `val` zeros from a word procedure for `val`**, as a relocatable writer
(the word procedure is its helper). Section 15 is this for `numConn`. -/
def zeroValW {a : ℕ} (V : ValW a) : SecW a where
  body k := zeroCallWriter k
  helpers _ := [V.body]
  l S G base := List.replicate (V.val S G base) 0
  cost _ G _ := V.cost G + 20
  noRand _ := ⟨by simp [zeroCallWriter, Stmt.NoRand], by simpa using V.noRand⟩
  spec w p f k hp hh S G := by
    have hV : p.procs[k]? = some V.body := by simpa using hh 0 (by simp)
    refine meetsContract_of_runs hp fun args mem pos ω hw hpre => ?_
    obtain ⟨base, c, rfl, hbl, hI, hz, hc, hcw⟩ := hpre
    simp only [List.length_replicate] at hcw
    have hargs : evalArgs w (startState (base ++ [c]) mem pos) secArgs = some (base ++ [c]) := by
      rw [evalArgs_secArgs]
      match base, hbl with
      | [a0, a1, a2, a3, a4, a5], _ => rfl
    have h6 : (startState (base ++ [c]) mem pos).regs 6 = c := by
      match base, hbl with
      | [a0, a1, a2, a3, a4, a5], _ => rfl
    refine runs_start_le ?_
    unfold zeroCallWriter
    refine runs_seq_call_le (V.spec w p k hV S G) hargs hw ⟨base, c, rfl, hbl, hI⟩ ?_
    intro v mem' pos' hpost
    obtain ⟨base', c', hargs', hv, hmem⟩ := hpost
    have hbb : base' = base := by
      have hl : base'.length = base.length := by
        have := congrArg List.length hargs'
        simp at this; omega
      exact (List.append_inj hargs'.symm hl).1
    subst hbb hv hmem
    refine runs_ret_le (v := c + V.val S G base')
      (Expr.eval_add (Expr.eval_reg_of_eq (by simp [Function.update, h6]))
        (Expr.eval_reg_of_eq (by simp)) hcw)
      ⟨base', c, rfl, by simp [Outcome.value], ?_, ?_, fun _ _ => rfl⟩ ?_
    · intro i hi
      simp only [List.length_replicate] at hi
      simp only [List.getElem_replicate]
      exact hz (c + i) (by omega)
    · intro y hy
      simp only [Outcome.value] at hy
      exact hz y (by omega)
    · simp only [SecContract, ValContract, secArgs, argsSize, Expr.size]
      omega

/-- Section 15 of the initial block (the ineligible bits) is `numConn` zeros. -/
theorem initConcrete_section_inelig (S : StaticData) (a : ℕ) (s : PathDSAbsState) :
    (initConcrete S a s).sections.getD 15 [] =
      List.replicate (initConcrete S a s).H.A.C.numConn 0 := by
  simp [HierConcrete.sections, initConcrete, DelState.init, bitsList, List.map_const']

end MinCostFlow.HierPaths

end
