module

public import MinCostFlow.SparseCore.Program.BunRestartKeys

/-!
# The restart of the bundles: tools for the proof of the run (`BunRestartLib`)

* `runs_forRange_amort`: a counter loop whose rounds are paid against a potential. Each round may
  cost more than a fixed bound `K`, if it lowers the potential `Φ` by the excess. The potential
  depends on a value `g` (for example the concrete state of the tour) that the invariant carries.
* `runs_seq_normal`: two runs one after the other.
* `BRRegs`, `BRRegsL`: the registers that the restart sets at its start and after loop A, kept
  by every later step.
-/

namespace MinCostFlow.SparseCore.Program.Restart

open WordRAM MinCostFlow.Bundle MinCostFlow.SparseCore MinCostFlow.Chain
open MinCostFlow.DynSpanner.Program MinCostFlow.SparseCore.Program

public section

/-- Two runs one after the other. -/
theorem runs_seq_normal {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt} {st st₁ st₂ : State}
    {o : Outcome} {c₁ c₂ : ℕ} (h₁ : Runs w p ω s st .normal st₁ c₁)
    (h₂ : Runs w p ω t st₁ o st₂ c₂) : Runs w p ω (s ;; t) st o st₂ (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, h₂, rfl⟩)

/-- A call followed by a statement, from a run of the called body. -/
theorem runs_seq_call_of_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {s : Stmt} {st : State} {vs : List ℕ} {body : Stmt} {o₁ o : Outcome} {st₁ st' : State}
    {c₁ c₂ : ℕ} (hargs : evalArgs w st args = some vs) (hproc : p.procs[f]? = some body)
    (hrun : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁)
    (hrest : Runs w p ω s { st₁ with regs := Function.update st.regs r o₁.value } o st' c₂) :
    Runs w p ω (.call r f args ;; s) st o st' (argsSize args + c₁ + 1 + c₂ + 1) :=
  runs_seq_normal (runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hrun, rfl, rfl, rfl⟩)
    hrest

/-- A run in the forward form of the tactics that ends normally. -/
theorem normal_of_fwd {w : ℕ} {p : Program} {ω : ℕ → Bool} {s : Stmt} {st : State}
    {P : State → Prop} {K : ℕ}
    (h : ∃ o st₁ c, Runs w p ω s st o st₁ c ∧ normalPost P o st₁ ∧ 0 + c ≤ K) :
    ∃ st₁ c, Runs w p ω s st .normal st₁ c ∧ P st₁ ∧ c ≤ K := by
  obtain ⟨o, st₁, c, hr, hq, hc⟩ := h
  cases o with
  | normal => exact ⟨st₁, c, hr, hq, by omega⟩
  | returned v => exact hq.elim

/-- **A counter loop paid against a potential.** The loop `forRange r 0 hi body` runs `hiVal`
rounds. The invariant `Inv i g st` holds before round `i`, for a value `g` that the rounds may
change. Each round costs at most `K` plus the drop of the potential `Φ g mem`. Then the loop costs
at most `hiVal (K + |hi| + 8) + |hi| + 6` plus the drop of the potential over the whole loop. -/
theorem runs_forRange_amort {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {hi : Expr}
    {body : Stmt} {α : Type*} {Inv : ℕ → α → State → Prop} (Φ : α → (ℕ → ℕ) → ℕ)
    (K hiVal : ℕ) (hw : 1 < 2 ^ w) (hhi_word : hiVal < 2 ^ w)
    (hreg : ∀ i g st, i ≤ hiVal → Inv i g st → st.regs r = i)
    (hhi : ∀ i g st, i ≤ hiVal → Inv i g st → hi.eval w st = some hiVal)
    (hbody : ∀ i g st, i < hiVal → Inv i g st →
      ∃ st₁ c g₁, Runs w p ω body st .normal st₁ c ∧ st₁.regs r = i ∧
        Inv (i + 1) g₁ { st₁ with regs := Function.update st₁.regs r (i + 1) } ∧
        c + Φ g₁ st₁.mem ≤ K + Φ g st.mem)
    {st : State} {g : α} (hst : Inv 0 g { st with regs := Function.update st.regs r 0 }) :
    ∃ st' c g', Runs w p ω (forRange r (.const 0) hi body) st .normal st' c ∧ Inv hiVal g' st' ∧
      c + Φ g' st'.mem ≤ hiVal * (K + hi.size + 8) + hi.size + 6 + Φ g st.mem := by
  suffices hloop : ∀ k i g st, hiVal - i = k → i ≤ hiVal → Inv i g st →
      ∃ st' c g', Runs w p ω (forUp r hi body) st .normal st' c ∧ Inv hiVal g' st' ∧
        c + Φ g' st'.mem ≤ (hiVal - i) * (K + hi.size + 8) + hi.size + 3 + Φ g st.mem by
    obtain ⟨st', c, g', hr, hI, hc⟩ := hloop _ 0 g _ rfl (Nat.zero_le _) hst
    have h0 : (Expr.const 0).eval w st = some 0 := Expr.eval_const (by omega)
    have hasg : Runs w p ω (.assign r (.const 0)) st .normal
        { st with regs := Function.update st.regs r 0 } 2 :=
      runs_assign_iff.mpr ⟨0, h0, rfl, rfl, by simp⟩
    refine ⟨st', 2 + c + 1, g', runs_seq_normal hasg hr, hI, ?_⟩
    simp only [Nat.sub_zero] at hc
    have : Φ g { st with regs := Function.update st.regs r 0 }.mem = Φ g st.mem := rfl
    omega
  intro k
  induction k with
  | zero =>
    intro i g st hk hile hInv
    have hle : i = hiVal := by omega
    subst hle
    have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 0 :=
      Expr.eval_lt_false (by simp [Expr.eval, hreg i g st hile hInv]) (hhi i g st hile hInv) le_rfl
        hw
    have hcost : (.bin .lt (.reg r) hi : Expr).size + 1 = hi.size + 3 := by simp; omega
    refine ⟨st, hi.size + 3, g, runs_loop_iff.mpr (Or.inl ⟨hcond, rfl, rfl, hcost.symm⟩), hInv,
      by omega⟩
  | succ k ih =>
    intro i g st hk hile hInv
    have hlt : i < hiVal := by omega
    have hcond : (Expr.bin .lt (.reg r) hi).eval w st = some 1 :=
      Expr.eval_lt_true (by simp [Expr.eval, hreg i g st hile hInv]) (hhi i g st hile hInv) hlt hw
    have hcondSize : (Expr.bin .lt (.reg r) hi : Expr).size = hi.size + 2 := by simp; omega
    obtain ⟨st₁, c₁, g₁, hr₁, hreg₁, hInv₁, hc₁⟩ := hbody i g st hlt hInv
    have hincEval : (Expr.bin .add (.reg r) (.const 1)).eval w st₁ = some (i + 1) :=
      Expr.eval_add (by simp [Expr.eval, hreg₁]) (Expr.eval_const hw) (by omega)
    have hinc : Runs w p ω (.assign r (.bin .add (.reg r) (.const 1))) st₁ .normal
        { st₁ with regs := Function.update st₁.regs r (i + 1) } 4 :=
      runs_assign_iff.mpr ⟨i + 1, hincEval, rfl, rfl, by simp⟩
    have hseq := runs_seq_normal hr₁ hinc
    obtain ⟨st₂, c₂, g₂, hr₂, hI₂, hc₂⟩ := ih (i + 1) g₁ _ (by omega) (by omega) hInv₁
    refine ⟨st₂, hi.size + 2 + (c₁ + 4 + 1) + c₂ + 1, g₂, ?_, hI₂, ?_⟩
    · exact runs_loop_iff.mpr (Or.inr (Or.inr ⟨1, _, c₁ + 4 + 1, c₂, hcond, by decide, hseq, hr₂,
        by omega⟩))
    · have hm : Φ g₁ { st₁ with regs := Function.update st₁.regs r (i + 1) }.mem =
          Φ g₁ st₁.mem := rfl
      rw [hm] at hc₂
      rw [show hiVal - i = (hiVal - (i + 1)) + 1 by omega, Nat.add_one_mul]
      omega

/-- A counter loop whose rounds have a fixed cost bound (`runs_forRange_amort` without
potential). -/
theorem runs_forRange_const {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {hi : Expr}
    {body : Stmt} {Inv : ℕ → State → Prop} (K hiVal : ℕ) (hw : 1 < 2 ^ w)
    (hhi_word : hiVal < 2 ^ w)
    (hreg : ∀ i st, i ≤ hiVal → Inv i st → st.regs r = i)
    (hhi : ∀ i st, i ≤ hiVal → Inv i st → hi.eval w st = some hiVal)
    (hbody : ∀ i st, i < hiVal → Inv i st →
      ∃ st₁ c, Runs w p ω body st .normal st₁ c ∧ (st₁.regs r = i ∧
        Inv (i + 1) { st₁ with regs := Function.update st₁.regs r (i + 1) }) ∧ c ≤ K)
    {st : State} (hst : Inv 0 { st with regs := Function.update st.regs r 0 }) :
    ∃ st' c, Runs w p ω (forRange r (.const 0) hi body) st .normal st' c ∧ Inv hiVal st' ∧
      c ≤ hiVal * (K + hi.size + 8) + hi.size + 6 := by
  obtain ⟨st', c, -, hr, hI, hc⟩ := runs_forRange_amort (Inv := fun i (_ : Unit) st => Inv i st)
    (fun _ _ => 0) K hiVal hw hhi_word (fun i _ st hle h => hreg i st hle h)
    (fun i _ st hle h => hhi i st hle h)
    (fun i _ st hle h => by
      obtain ⟨st₁, c, hr, ⟨hreg₁, hI₁⟩, hc⟩ := hbody i st hle h
      exact ⟨st₁, c, (), hr, hreg₁, hI₁, by omega⟩) (g := ()) hst
  exact ⟨st', c, hr, hI, by omega⟩

/-! ## Lists in memory and sums -/

theorem listAt_append' {mem : ℕ → ℕ} {a : ℕ} {l₁ l₂ : List ℕ} (h₁ : ListAt mem a l₁)
    (h₂ : ListAt mem (a + l₁.length) l₂) : ListAt mem a (l₁ ++ l₂) := by
  intro i hi
  by_cases hil : i < l₁.length
  · rw [List.getElem_append_left hil]; exact h₁ i hil
  · rw [List.getElem_append_right (by omega)]
    have := h₂ (i - l₁.length) (by simp at hi; omega)
    rwa [show a + l₁.length + (i - l₁.length) = a + i by omega] at this

theorem listAt_congr' {mem mem' : ℕ → ℕ} {a : ℕ} {l : List ℕ} (h : ListAt mem a l)
    (hag : ∀ i < l.length, mem' (a + i) = mem (a + i)) : ListAt mem' a l :=
  fun i hi => (hag i hi).trans (h i hi)

theorem brSum_range_getD (l : List ℕ) (f : ℕ → ℕ) :
    ((List.range l.length).map fun i => f (l.getD i 0)).sum = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons x l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.map_cons, List.map_map, List.sum_cons,
      List.map_cons, List.sum_cons]
    simp only [List.getD_cons_zero, Function.comp_def, List.getD_cons_succ]
    rw [ih]

theorem length_flatMap_take_succ {α : Type*} {l : List ℕ} {f : ℕ → List α} {i : ℕ}
    (hi : i < l.length) :
    (l.take (i + 1)).flatMap f = (l.take i).flatMap f ++ f l[i] := by
  rw [List.take_succ_eq_append_getElem hi, List.flatMap_append, List.flatMap_singleton]

theorem length_flatMap_take_le {α : Type*} (l : List ℕ) (f : ℕ → List α) (i : ℕ) :
    ((l.take i).flatMap f).length ≤ (l.flatMap f).length := by
  conv_rhs => rw [← List.take_append_drop i l]
  rw [List.flatMap_append, List.length_append]
  omega

/-! ## The registers of the restart -/

/-- The registers set at the start of the restart: the arguments `[tbl, tourH, n, slotsPtr, h]`,
the slot pointer base, the edge slot base and the end-next base of the table, and the specs
pointer `h + 4 n`. Only registers `0`–`8`. -/
structure BRRegs (regs : ℕ → ℕ) (tbl tourH n slotsPtr h slotCap eCap : ℕ) : Prop where
  r0 : regs 0 = tbl
  r1 : regs 1 = tourH
  r2 : regs 2 = n
  r3 : regs 3 = slotsPtr
  r4 : regs 4 = h
  r5 : regs 5 = btSlotPtrBase tbl
  r6 : regs 6 = btEdgeSlotBase tbl slotCap
  r7 : regs 7 = btEndNextBase tbl slotCap eCap
  r8 : regs 8 = h + 4 * n

theorem BRRegs.upd {regs : ℕ → ℕ} {tbl tourH n slotsPtr h slotCap eCap : ℕ}
    (hR : BRRegs regs tbl tourH n slotsPtr h slotCap eCap) {r v : ℕ} (hr : 8 < r) :
    BRRegs (Function.update regs r v) tbl tourH n slotsPtr h slotCap eCap := by
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8⟩ := hR
  exact ⟨by rwa [Function.update_of_ne (by omega)], by rwa [Function.update_of_ne (by omega)],
    by rwa [Function.update_of_ne (by omega)], by rwa [Function.update_of_ne (by omega)],
    by rwa [Function.update_of_ne (by omega)], by rwa [Function.update_of_ne (by omega)],
    by rwa [Function.update_of_ne (by omega)], by rwa [Function.update_of_ne (by omega)],
    by rwa [Function.update_of_ne (by omega)]⟩

theorem BRRegs.of_eq {regs regs' : ℕ → ℕ} {tbl tourH n slotsPtr h slotCap eCap : ℕ}
    (hR : BRRegs regs tbl tourH n slotsPtr h slotCap eCap) (hag : ∀ r ≤ 8, regs' r = regs r) :
    BRRegs regs' tbl tourH n slotsPtr h slotCap eCap :=
  ⟨(hag 0 (by omega)).trans hR.r0, (hag 1 (by omega)).trans hR.r1, (hag 2 (by omega)).trans hR.r2,
    (hag 3 (by omega)).trans hR.r3, (hag 4 (by omega)).trans hR.r4, (hag 5 (by omega)).trans hR.r5,
    (hag 6 (by omega)).trans hR.r6, (hag 7 (by omega)).trans hR.r7, (hag 8 (by omega)).trans hR.r8⟩

/-- The registers set after loop A: the edge count `E` (register `9`) and the bases of the five
arrays of `2 E` words from `h + 6 n` on (registers `13`–`17`). -/
structure BRRegsL (regs : ℕ → ℕ) (h n E : ℕ) : Prop where
  r9 : regs 9 = E
  r13 : regs 13 = h + 6 * n
  r14 : regs 14 = h + 6 * n + 2 * E
  r15 : regs 15 = h + 6 * n + 4 * E
  r16 : regs 16 = h + 6 * n + 6 * E
  r17 : regs 17 = h + 6 * n + 8 * E

theorem BRRegsL.upd {regs : ℕ → ℕ} {h n E : ℕ} (hR : BRRegsL regs h n E) {r v : ℕ}
    (hr : r ≠ 9 ∧ r ≠ 13 ∧ r ≠ 14 ∧ r ≠ 15 ∧ r ≠ 16 ∧ r ≠ 17) :
    BRRegsL (Function.update regs r v) h n E := by
  obtain ⟨h9, h13, h14, h15, h16, h17⟩ := hR
  exact ⟨by rwa [Function.update_of_ne (by omega)], by rwa [Function.update_of_ne (by omega)],
    by rwa [Function.update_of_ne (by omega)], by rwa [Function.update_of_ne (by omega)],
    by rwa [Function.update_of_ne (by omega)], by rwa [Function.update_of_ne (by omega)]⟩

theorem BRRegsL.of_eq {regs regs' : ℕ → ℕ} {h n E : ℕ} (hR : BRRegsL regs h n E)
    (hag : ∀ r, (r = 9 ∨ (13 ≤ r ∧ r ≤ 17)) → regs' r = regs r) : BRRegsL regs' h n E :=
  ⟨(hag 9 (by omega)).trans hR.r9, (hag 13 (by omega)).trans hR.r13,
    (hag 14 (by omega)).trans hR.r14, (hag 15 (by omega)).trans hR.r15,
    (hag 16 (by omega)).trans hR.r16, (hag 17 (by omega)).trans hR.r17⟩

end

end MinCostFlow.SparseCore.Program.Restart
