module

public import MinCostFlow.SparseCore.Program.OutStepSplitModel

/-!
# One split of the output step, first part

A split round (`osSplitIter`) has three parts (`osSplitIter_eq`). The first part
(`osSplitA`) reads the split record `[v, v', side, ptr, next]` of the helper, writes a first
record of the split into the batch region from the ends of the list `Y` at `ptr` whose edge is
still in the graph (two filter calls and five header words), and applies it to the stored graph.
This file proves that the first part runs (`osSplitA_runs`).
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle MinCostFlow.DynSpanner.Program

/-- The first part of a split round, followed by `rest`. -/
def osSplitA (au flt : ℕ) (rest : Stmt) : Stmt :=
  .seq (.assign 21 (.load (.reg 20)))
  (.seq (.assign 22 (.load (.bin .add (.reg 20) (.const 1))))
  (.seq (.assign 27 (.load (.bin .add (.reg 20) (.const 2))))
  (.seq (.assign 28 (.load (.bin .add (.reg 20) (.const 3))))
  (.seq (osFilters flt (.bin .add (.reg 28) (.const 1)) (.load (.reg 28)))
  (.seq (osBHdr (.bin .sub (.const 3) (.reg 27)))
  (.seq (.call 9 au [.reg 10, .reg 14, .const 1]) rest))))))

/-- The second part: the degrees, the choice of the smaller side, the walk of its incidence list
and the head of the edit. -/
def osSplitB (gd wk : ℕ) (rest : Stmt) : Stmt :=
  .seq (.call 31 gd [.reg 10, .reg 22])
  (.seq (.call 32 gd [.reg 10, .reg 21])
  (.seq osChoose
  (.seq (.call 36 wk [.reg 25, .bin .add (.reg 24) (.load (.bin .add (.reg 23) (.reg 33))),
      .bin .add (.reg 16) (.const 4)])
  (.seq osEHdr rest))))

/-- The third part: the final record of the split from the keys of the edit, the two pointers,
and the next split record. -/
def osSplitC (flt : ℕ) : Stmt :=
  .seq (osFilters flt (.bin .add (.reg 16) (.const 4)) (.reg 36))
  (.seq (osBHdr (.reg 34))
  (.seq (osBumpB (.bin .add (.const 5) (.reg 36)))
  (.seq (osBumpE (.bin .add (.const 4) (.reg 36)))
    (.assign 20 (.load (.bin .add (.reg 20) (.const 4)))))))

theorem osSplitIter_eq (au gd flt wk : ℕ) :
    osSplitIter au gd flt wk = osSplitA au flt (osSplitB gd wk (osSplitC flt)) := rfl

/-- A step followed by a part whose cost has the form `K + c'`: the cost keeps this form. -/
theorem runs_seq_cont {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt} {st st₁ st₂ : State}
    {o : Outcome} {c₁ K c' : ℕ} (h₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (h₂ : Runs w p ω s₂ st₁ o st₂ (K + c')) : Runs w p ω (.seq s₁ s₂) st o st₂ (c₁ + K + 1 + c') := by
  have := runs_seq_normal h₁ h₂
  rwa [show c₁ + (K + c') + 1 = c₁ + K + 1 + c' by omega] at this

/-- The last step before the rest. -/
theorem runs_seq_last {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt} {st st₁ st₂ : State}
    {o : Outcome} {c₁ c' : ℕ} (h₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (h₂ : Runs w p ω s₂ st₁ o st₂ c') : Runs w p ω (.seq s₁ s₂) st o st₂ (c₁ + 1 + c') := by
  have := runs_seq_normal h₁ h₂
  rwa [show c₁ + c' + 1 = c₁ + 1 + c' by omega] at this

/-- The keys of a list of ends at `a + 1`. -/
theorem listAt_of_endListAt {mem : ℕ → ℕ} {a : ℕ} {Y : List End} (h : EndListAt mem a Y) :
    ListAt mem (a + 1) (Y.map endKey) := by
  intro i hi
  rw [List.length_map] at hi
  rw [h.2 i hi, List.getElem_map, List.getD_eq_getElem _ _ hi]

/-- The words of a list in memory are words when its entries are. -/
theorem ListAt.lt_of {mem : ℕ → ℕ} {a B : ℕ} {l : List ℕ} (h : ListAt mem a l)
    (hl : ∀ x ∈ l, x < B) : ∀ i < l.length, mem (a + i) < B := fun i hi => by
  rw [h i hi]; exact hl _ (List.getElem_mem hi)

/-- The five words of a record head, written one by one. -/
theorem listAt_five {mem : ℕ → ℕ} {a x₀ x₁ x₂ x₃ x₄ : ℕ} :
    ListAt (Function.update (Function.update (Function.update (Function.update
      (Function.update mem a x₀) (a + 1) x₁) (a + 2) x₂) (a + 3) x₃) (a + 4) x₄) a
      [x₀, x₁, x₂, x₃, x₄] := by
  intro i hi
  simp only [List.length_cons, List.length_nil] at hi
  interval_cases i <;> simp [Function.update_apply]

/-- The length of the two edge lists of a list whose edges are all present. -/
theorem endEdges_length_add {Y : List End} {E : Finset ℕ} (hY : ∀ x ∈ Y, x.1 ∈ E) :
    (endEdges Y E true).length + (endEdges Y E false).length = Y.length := by
  induction Y with
  | nil => rfl
  | cons x Y ih =>
    have ih' := ih fun y hy => hY y (List.mem_cons_of_mem _ hy)
    have hx := hY x List.mem_cons_self
    obtain ⟨e, b⟩ := x
    simp only at hx
    cases b <;> simp [endEdges, List.filter_cons, hx] at ih' ⊢ <;> omega

theorem endEdges_length_le {Y : List End} {E : Finset ℕ} (b : Bool) :
    (endEdges Y E b).length ≤ Y.length := by
  unfold endEdges
  rw [List.length_map]
  exact List.length_filter_le _ _

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ} {ω : ℕ → Bool}
  {T : OutTourAt S w vCap eCap p nm sm fm lm} {A : OSArgs} {tx₀ : T.rep.τ}
  {mem₀ : ℕ → ℕ} {S₀ G : MGraph} {U : List Update} {E : List OrdEdit} {bp ep cur : ℕ}
  {s : OutTourAbs} {tx : T.rep.τ}

/-- **The first part of a split round.** -/
theorem osSplitA_runs (hC : SCtx T A tx₀) {au flt : ℕ}
    (hau : ∀ G H u len, MeetsContract w p au (dgApplyUpdateContract w vCap eCap G H u len))
    (hflt : p.procs[flt]? = some outFilterBody)
    {st : State} {a v v' : ℕ} {St Sh : Finset ℕ} {Y : List End}
    (hB : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st.mem)
    (hR : SRegs st A vCap eCap) (h14 : st.regs 14 = bp) (h20 : st.regs 20 = a)
    (hw : (vCap + eCap + 2) ^ 2 < 2 ^ w) (ht0 : A.t0 < 2 ^ w)
    (ha5 : a + 5 ≤ A.h)
    (hafree : ∀ i < 5, ¬ ((outGraphRep vCap eCap).foot A.outH A.g (a + i) ∨
      T.rep.foot A.tourH tx₀ (a + i)))
    (hv : mem₀ a = v) (hv' : mem₀ (a + 1) = v') (hside : mem₀ (a + 2) ≤ 1)
    (hY : EndListAt mem₀ (mem₀ (a + 3)) Y) (hptr : mem₀ (a + 3) + 1 + Y.length ≤ A.h)
    (hpfree : ∀ i < 1 + Y.length, ¬ ((outGraphRep vCap eCap).foot A.outH A.g (mem₀ (a + 3) + i) ∨
      T.rep.foot A.tourH tx₀ (mem₀ (a + 3) + i)))
    (hnd : Y.Nodup) (hYc : ∀ x ∈ Y, x.1 < eCap)
    (hYs : ∀ x : End, x.1 ∈ G.E →
      (x ∈ Y ↔ (G.applyUpdate (.split v v' St Sh)).src x = if mem₀ (a + 2) = 0 then v else v'))
    (hval : G.UpdateIsValid (.split v v' St Sh)) (hv'c : v' < vCap)
    (hbk : bp + 5 + 2 * Y.length ≤ A.e0) :
    ∃ stA cA, (∀ rest o st'' c', Runs w p ω rest stA o st'' c' →
        Runs w p ω (osSplitA au flt rest) st o st'' (cA + c')) ∧
      SBase T A tx₀ mem₀ S₀ (G.applyUpdate (.split v v' St Sh)) U E bp ep cur s tx stA.mem ∧
      T.rep.phi A.tourH tx stA.mem = T.rep.phi A.tourH tx st.mem ∧
      (∀ r, r ≠ 21 → r ≠ 22 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → r ≠ 9 →
        stA.regs r = st.regs r) ∧
      stA.regs 21 = v ∧ stA.regs 22 = v' ∧ cA ≤ 2000 * Y.length + 4000 := by
  have hR' := hR
  obtain ⟨-, -, -, -, -, -, -, r10, -, -, -, -, r19, -, -, -⟩ := hR'
  have hgh := hC.2.2.1
  have hkey := rs_key_lt hw
  have hvw : vCap + eCap + 2 < 2 ^ w := lt_of_le_of_lt (Nat.le_self_pow two_ne_zero _) hw
  have hR0 : A.e0 = A.h + 4 + A.R := rfl
  have ht0e : A.t0 = A.e0 + A.R := rfl
  have hbp1 := hB.2.2.2.2.2.2.2.1
  have hbp2 := hB.2.2.2.2.2.2.2.2.1
  have hep1 := hB.2.2.2.2.2.2.2.2.2.2.1
  have hep2 := hB.2.2.2.2.2.2.2.2.2.2.2.1
  have h9 : 9 ≤ (vCap + eCap + 2) ^ 2 := Nat.pow_le_pow_left (by omega : 3 ≤ vCap + eCap + 2) 2
  have hG := hB.2.2.2.2.2.2.1
  have hGval := hG.1
  have hGE := hG.2.2.1
  have hpres := hG.2.2.2.2.2.2.2.2.2.2.2.1
  have hsize : dgEPresBase A.g vCap + 2 * eCap ≤ A.g + dynGraphSize vCap eCap := by
    unfold dgEPresBase dynGraphSize; omega
  have hvc : v < vCap := hG.2.1 v hval.1
  set ptr := mem₀ (a + 3) with hptr_def
  set side := mem₀ (a + 2) with hside_def
  set pb := dgEPresBase A.g vCap with hpb
  -- the record words
  have hrd : ∀ i < 5, st.mem (a + i) = mem₀ (a + i) := fun i hi => hB.mem_eq (by omega) (hafree i hi)
  have hptrm : st.mem ptr = Y.length := by
    rw [hB.mem_eq (by omega) (by simpa using hpfree 0 (by omega))]; exact hY.1
  have hK : ListAt st.mem (ptr + 1) (Y.map endKey) := by
    intro i hi
    rw [List.length_map] at hi
    rw [hB.mem_eq (by omega) (by
      have := hpfree (1 + i) (by omega); rwa [show ptr + (1 + i) = ptr + 1 + i by omega] at this)]
    exact listAt_of_endListAt hY i (by simpa using hi)
  obtain ⟨st₁, hr₁, hm₁, h21₁, ho₁⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 21)
    (e := .load (.reg 20)) (st := st) (v := v)
    (Expr.eval_load_of_eq (Expr.eval_reg_of_eq h20) (by rw [← hv]; simpa using hrd 0 (by omega)))
  obtain ⟨st₂, hr₂, hm₂, h22₂, ho₂⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 22)
    (e := .load (.bin .add (.reg 20) (.const 1))) (st := st₁) (v := v')
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₁ 20 (by omega), h20]))
      (Expr.eval_const (by omega)) (by omega)) (by rw [hm₁, ← hv']; exact hrd 1 (by omega)))
  obtain ⟨st₃, hr₃, hm₃, h27₃, ho₃⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 27)
    (e := .load (.bin .add (.reg 20) (.const 2))) (st := st₂) (v := side)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₂ 20 (by omega),
      ho₁ 20 (by omega), h20])) (Expr.eval_const (by omega)) (by omega))
      (by rw [hm₂, hm₁, hrd 2 (by omega)]))
  obtain ⟨st₄, hr₄, hm₄, h28₄, ho₄⟩ := step_assign (w := w) (p := p) (ω := ω) (r := 28)
    (e := .load (.bin .add (.reg 20) (.const 3))) (st := st₃) (v := ptr)
    (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₃ 20 (by omega),
      ho₂ 20 (by omega), ho₁ 20 (by omega), h20])) (Expr.eval_const (by omega)) (by omega))
      (by rw [hm₃, hm₂, hm₁, hrd 3 (by omega)]))
  have g : ∀ r, r ≠ 21 → r ≠ 22 → r ≠ 27 → r ≠ 28 → st₄.regs r = st.regs r :=
    fun r a b c d => by rw [ho₄ r d, ho₃ r c, ho₂ r b, ho₁ r a]
  have hm₄' : st₄.mem = st.mem := by rw [hm₄, hm₃, hm₂, hm₁]
  have h28' : st₄.regs 28 = ptr := h28₄
  have hB₄ : SBase T A tx₀ mem₀ S₀ G U E bp ep cur s tx st₄.mem := by rw [hm₄']; exact hB
  -- the first filter: the tail edges
  have hlt0 : keyFilterMem st.mem pb (Y.map endKey) 0 = endEdges Y G.E true :=
    keyFilterMem_endEdges (b := true) hpres hYc
  obtain ⟨st₅, c₅, hr₅, hB₅, hp₅, hL₅, hag₅, h29₅, ho₅, hc₅⟩ := os_filter (ω := ω) (r := 29)
    (args := [.bin .add (.reg 28) (.const 1), .load (.reg 28), .const 0,
      .bin .add (.reg 14) (.const 5), .reg 19]) hC hflt hB₄
    (evalArgs_five (Expr.eval_add (Expr.eval_reg_of_eq h28') (Expr.eval_const (by omega))
      (by omega)) (Expr.eval_load_of_eq (Expr.eval_reg_of_eq h28') (by rw [hm₄']; exact hptrm))
      (Expr.eval_const (by omega)) (Expr.eval_add (Expr.eval_reg_of_eq (by
        rw [g 14 (by omega) (by omega) (by omega) (by omega), h14])) (Expr.eval_const (by omega))
        (by omega)) (Expr.eval_reg_of_eq (by rw [g 19 (by omega) (by omega) (by omega) (by omega),
        r19])))
    (by rw [hm₄']; exact hK) (List.length_map _)
    (fun k hk => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      have := endKey_lt_two_mul (hYc x hx); omega)
    (by omega) (by omega) (by omega) (fun i hi j hj => by omega)
    (fun k hk j hj => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      have := endKey_lt_two_mul (hYc x hx); omega)
    (fun j hj => ⟨by omega, by omega, by omega, by omega⟩)
  rw [hm₄', hlt0] at hL₅ h29₅
  set Lt := endEdges Y G.E true with hLt
  have hLtle : Lt.length ≤ Y.length := endEdges_length_le true
  -- the second filter: the head edges
  have hlt1 : keyFilterMem st₅.mem pb (Y.map endKey) 1 = endEdges Y G.E false :=
    keyFilterMem_endEdges (b := false) hB₅.2.2.2.2.2.2.1.2.2.2.2.2.2.2.2.2.2.2.1 hYc
  have hK₅ : ListAt st₅.mem (ptr + 1) (Y.map endKey) := fun i hi => by
    rw [hag₅ _ (by simp at hi; omega), hm₄']; exact hK i hi
  have hptrm₅ : st₅.mem ptr = Y.length := by rw [hag₅ _ (by omega), hm₄']; exact hptrm
  obtain ⟨st₆, c₆, hr₆, hB₆, hp₆, hL₆, hag₆, h30₆, ho₆, hc₆⟩ := os_filter (ω := ω) (r := 30)
    (args := [.bin .add (.reg 28) (.const 1), .load (.reg 28), .const 1,
      .bin .add (.bin .add (.reg 14) (.const 5)) (.reg 29), .reg 19]) hC hflt hB₅
    (evalArgs_five (Expr.eval_add (Expr.eval_reg_of_eq (by rw [ho₅ 28 (by omega), h28']))
      (Expr.eval_const (by omega)) (by omega))
      (Expr.eval_load_of_eq (Expr.eval_reg_of_eq (by rw [ho₅ 28 (by omega), h28'])) hptrm₅)
      (Expr.eval_const (by omega))
      (Expr.eval_add (Expr.eval_add (Expr.eval_reg_of_eq (by
        rw [ho₅ 14 (by omega), g 14 (by omega) (by omega) (by omega) (by omega), h14]))
        (Expr.eval_const (by omega)) (by omega)) (Expr.eval_reg_of_eq h29₅) (by omega))
      (Expr.eval_reg_of_eq (by rw [ho₅ 19 (by omega), g 19 (by omega) (by omega) (by omega)
        (by omega), r19])))
    hK₅ (List.length_map _)
    (fun k hk => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      have := endKey_lt_two_mul (hYc x hx); omega)
    (by omega) (by omega) (by omega) (fun i hi j hj => by omega)
    (fun k hk j hj => by
      obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hk
      have := endKey_lt_two_mul (hYc x hx); omega)
    (fun j hj => ⟨by omega, by omega, by omega, by omega⟩)
  rw [hlt1] at hL₆ h30₆
  set Lh := endEdges Y G.E false with hLh
  have hLhle : Lh.length ≤ Y.length := endEdges_length_le false
  -- the five head words
  have g₆ : ∀ r, r ≠ 21 → r ≠ 22 → r ≠ 27 → r ≠ 28 → r ≠ 29 → r ≠ 30 → st₆.regs r = st.regs r :=
    fun r a b c d e f => by rw [ho₆ r f, ho₅ r e, g r a b c d]
  have g14 : st₆.regs 14 = bp := by
    rw [g₆ 14 (by omega) (by omega) (by omega) (by omega) (by omega) (by omega), h14]
  have g21 : st₆.regs 21 = v := by rw [ho₆ 21 (by omega), ho₅ 21 (by omega), ho₄ 21 (by omega),
    ho₃ 21 (by omega), ho₂ 21 (by omega), h21₁]
  have g22 : st₆.regs 22 = v' := by rw [ho₆ 22 (by omega), ho₅ 22 (by omega), ho₄ 22 (by omega),
    ho₃ 22 (by omega), h22₂]
  have g27 : st₆.regs 27 = side := by rw [ho₆ 27 (by omega), ho₅ 27 (by omega),
    ho₄ 27 (by omega), h27₃]
  have g29 : st₆.regs 29 = Lt.length := by rw [ho₆ 29 (by omega), h29₅]
  obtain ⟨st₇, hr₇, hB₇, hp₇, hm₇, hg₇⟩ := os_store (p := p) (ω := ω) (a := .reg 14)
    (e := .bin .sub (.const 3) (.reg 27)) hC hB₆ (Expr.eval_reg_of_eq g14)
    (Expr.eval_sub (Expr.eval_const (k := 3) (by omega)) (Expr.eval_reg_of_eq g27) (by omega))
    ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₈, hr₈, hB₈, hp₈, hm₈, hg₈⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 1)) (e := .reg 21) hC hB₇
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₇, g14])) (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₇, g21])) ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₉, hr₉, hB₉, hp₉, hm₉, hg₉⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 2)) (e := .reg 22) hC hB₈
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₈, hg₇, g14])) (Expr.eval_const (by omega))
      (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₈, hg₇, g22])) ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₁₀, hr₁₀, hB₁₀, hp₁₀, hm₁₀, hg₁₀⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 3)) (e := .reg 29) hC hB₉
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₉, hg₈, hg₇, g14])) (Expr.eval_const (by omega))
      (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₉, hg₈, hg₇, g29])) ⟨by omega, by omega, by omega, by omega⟩
  obtain ⟨st₁₁, hr₁₁, hB₁₁, hp₁₁, hm₁₁, hg₁₁⟩ := os_store (p := p) (ω := ω)
    (a := .bin .add (.reg 14) (.const 4)) (e := .reg 30) hC hB₁₀
    (Expr.eval_add (Expr.eval_reg_of_eq (by rw [hg₁₀, hg₉, hg₈, hg₇, g14]))
      (Expr.eval_const (by omega)) (by omega))
    (Expr.eval_reg_of_eq (by rw [hg₁₀, hg₉, hg₈, hg₇, h30₆]))
    ⟨by omega, by omega, by omega, by omega⟩
  -- the record of the split
  have hrec : ListAt st₁₁.mem bp ([3 - side, v, v', Lt.length, Lh.length] ++ Lt ++ Lh) := by
    have hhdr : ListAt st₁₁.mem bp [3 - side, v, v', Lt.length, Lh.length] := by
      rw [hm₁₁, hm₁₀, hm₉, hm₈, hm₇]; exact listAt_five
    have hag : ∀ x, ¬ (bp ≤ x ∧ x < bp + 5) → st₁₁.mem x = st₆.mem x := by
      intro x hx
      rw [hm₁₁, hm₁₀, hm₉, hm₈, hm₇]
      simp only [Function.update_apply]
      split_ifs <;> first | rfl | omega
    refine listAt_append.mpr ⟨listAt_append.mpr ⟨hhdr, fun i hi => ?_⟩, fun i hi => ?_⟩
    · simp only [List.length_cons, List.length_nil] at hi ⊢
      rw [hag _ (by omega), hag₆ _ (by omega)]
      exact hL₅ i hi
    · simp only [List.length_append, List.length_cons, List.length_nil] at hi ⊢
      rw [hag _ (by omega), show bp + (5 + Lt.length) + i = bp + 5 + Lt.length + i by omega]
      exact hL₆ i hi
  have hu := updateAt_split_of_lists (a := bp) hGval hval hnd side hside hYs hrec
  rw [← hLt, ← hLh] at hu
  have hLtc : ∀ e ∈ Lt, e < eCap := fun e he => hGE e ((mem_endEdges.mp he).2)
  have hLhc : ∀ e ∈ Lh, e < eCap := fun e he => hGE e ((mem_endEdges.mp he).2)
  have hrecw : ∀ x ∈ [3 - side, v, v', Lt.length, Lh.length] ++ Lt ++ Lh, x < 2 ^ w := by
    intro x hx
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with ((rfl | rfl | rfl | rfl | rfl) | hx) | hx
    · omega
    · omega
    · omega
    · omega
    · omega
    · have := hLtc x hx; omega
    · have := hLhc x hx; omega
  have hreclen : ([3 - side, v, v', Lt.length, Lh.length] ++ Lt ++ Lh).length =
      5 + Lt.length + Lh.length := by
    simp only [List.length_append, List.length_cons, List.length_nil]
  obtain ⟨st₁₂, c₁₂, hr₁₂, hB₁₂, hp₁₂, hfr₁₂, ho₁₂, hc₁₂⟩ := os_apply (ω := ω) hC hau hB₁₁
    (by rw [hg₁₁, hg₁₀, hg₉, hg₈, hg₇, g₆ 10 (by omega) (by omega) (by omega) (by omega) (by omega)
      (by omega), r10])
    (by rw [hg₁₁, hg₁₀, hg₉, hg₈, hg₇, g14]) hu hval hv'c (by omega)
    (fun i hi => ListAt.lt_of hrec hrecw i (by rw [hreclen]; exact hi))
    (rs_sixteen_le (by omega)) (by omega) (by omega)
  have hrun := fun rest o st'' c' (hrest : Runs w p ω rest st₁₂ o st'' c') =>
    runs_seq_cont hr₁ (runs_seq_cont hr₂ (runs_seq_cont hr₃ (runs_seq_cont hr₄
      (runs_seq_cont (runs_seq_normal hr₅ hr₆) (runs_seq_cont (runs_seq_normal hr₇
        (runs_seq_normal hr₈ (runs_seq_normal hr₉ (runs_seq_normal hr₁₀ hr₁₁))))
        (runs_seq_last hr₁₂ hrest))))))
  refine ⟨st₁₂, _, hrun, hB₁₂, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hp₁₂, hp₁₁, hp₁₀, hp₉, hp₈, hp₇, hp₆, hp₅, hm₄']
  · intro r a b c d e f h9
    rw [ho₁₂ r h9, hg₁₁, hg₁₀, hg₉, hg₈, hg₇, g₆ r a b c d e f]
  · rw [ho₁₂ 21 (by omega), hg₁₁, hg₁₀, hg₉, hg₈, hg₇, g21]
  · rw [ho₁₂ 22 (by omega), hg₁₁, hg₁₀, hg₉, hg₈, hg₇, g22]
  · simp only [argsSize, Expr.size_reg, Expr.size_bin, Expr.size_const,
      Expr.size_load] at hc₅ hc₆ hc₁₂ ⊢
    omega

end MinCostFlow.SparseCore.Program
