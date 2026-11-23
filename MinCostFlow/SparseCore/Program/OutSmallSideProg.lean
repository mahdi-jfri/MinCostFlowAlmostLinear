module

public import MinCostFlow.SparseCore.Program.OutStepSpec
public import MinCostFlow.SparseCore.Program.OutSmallSideWalk
public import MinCostFlow.SparseCore.Program.OrdStoreCapContract
public import MinCostFlow.LowStretch.ProgAmort

/-!
# The program of the helper `outSmallSide`

The helper of piece P7 (`sig_outSmallSide_runs`) is called right after a cut of a core tree. It
must list the marked ends of the smaller of the two parts, and pay only for that part. It walks
the marked ends of both parts in turn: first the first marked end of each part
(`firstMarked`), then at each round the next marked end of each part (`nextMarked`). A part is
done when its walk comes back to its first marked end. The first part that is done is the
smaller one, and the walk has made at most twice as many steps as it has marked ends. Then the
helper lists that part (`listMarked`) and copies the list to the end of the heap, after every
cell that the tour may have taken.

This file has the program (`outSmallSideBody`), small run lemmas, and the frame that every tour
call keeps (`SSFrame`). The proof is in `OutSmallSide.lean`.

Registers: `0`–`6` hold the arguments `[tourH, r₁, r₂, v, v', last, h]`, `7` the heap pointer,
`8` the result of a call, `9` and `10` the codes of the first marked ends, `11` the side, `12` and
`13` the codes of the current ends of the walk, `14` the flag of the walk, `16` the chosen root,
`18` the length of its list, and `19` the counter of the copy.
-/

@[expose] public section

namespace MinCostFlow.SparseCore.Program

open WordRAM MinCostFlow.Bundle

/-! ## Small run lemmas -/

theorem runs_seq_normal {w : ℕ} {p : Program} {ω : ℕ → Bool} {s₁ s₂ : Stmt} {st st₁ st₂ : State}
    {o : Outcome} {c₁ c₂ : ℕ} (h₁ : Runs w p ω s₁ st .normal st₁ c₁)
    (h₂ : Runs w p ω s₂ st₁ o st₂ c₂) : Runs w p ω (.seq s₁ s₂) st o st₂ (c₁ + c₂ + 1) :=
  runs_seq_iff.mpr (Or.inr ⟨st₁, c₁, c₂, h₁, h₂, rfl⟩)

theorem runs_assign_of {w : ℕ} {p : Program} {ω : ℕ → Bool} {r : ℕ} {e : Expr} {st : State}
    {v : ℕ} (he : e.eval w st = some v) :
    Runs w p ω (.assign r e) st .normal { st with regs := Function.update st.regs r v }
      (e.size + 1) :=
  runs_assign_iff.mpr ⟨v, he, rfl, rfl, rfl⟩

theorem runs_store_of {w : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr} {st : State}
    {x v : ℕ} (ha : a.eval w st = some x) (he : e.eval w st = some v) :
    Runs w p ω (.store a e) st .normal { st with mem := Function.update st.mem x v }
      (a.size + e.size + 1) :=
  runs_store_iff.mpr ⟨x, v, ha, he, rfl, rfl, rfl⟩

theorem runs_call_of {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ} {args : List Expr}
    {st : State} {vs : List ℕ} {body : Stmt} {o₁ : Outcome} {st₁ : State} {c₁ : ℕ}
    (hargs : evalArgs w st args = some vs) (hproc : p.procs[f]? = some body)
    (hrun : Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁) :
    Runs w p ω (.call r f args) st .normal { st₁ with regs := Function.update st.regs r o₁.value }
      (argsSize args + c₁ + 1) :=
  runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hrun, rfl, rfl, rfl⟩

/-! ## The program -/

/-- A tour query `[tourH, arg, heap]` at procedure `f`; its answer goes to register `dst`, and the
heap pointer moves past the cells of the call. -/
def ssQuery (f : ℕ) (argE : Expr) (dst : ℕ) : Stmt :=
  .seq (.call 8 f [.reg 0, argE, .reg 7])
    (.seq (.assign dst (.load (.reg 7))) (.assign 7 (.reg 8)))

/-- Write `v` and `v'` in the record, link it after the record `last`, and start the heap after
the record. -/
def ssHead : Stmt :=
  .seq (.store (.reg 6) (.reg 3))
    (.seq (.store (.bin .add (.reg 6) (.const 1)) (.reg 4))
      (.seq (.cond (.reg 5) (.store (.bin .add (.reg 5) (.const 4)) (.reg 6)) .nop)
        (.assign 7 (.bin .add (.reg 6) (.const 5)))))

/-- The side is `0` and the walk is off when the first part has no marked end, the side is `1`
and the walk is off when only the second part has none, and otherwise the walk is on. -/
def ssInit : Stmt :=
  .seq (.assign 11 (.const 0))
    (.seq (.assign 14 (.const 0))
      (.seq (.cond (.bin .eq (.reg 9) (.const 0)) .nop
          (.cond (.bin .eq (.reg 10) (.const 0)) (.assign 11 (.const 1)) (.assign 14 (.const 1))))
        (.seq (.assign 12 (.reg 9)) (.assign 13 (.reg 10)))))

/-- One round of the walk: the next marked end of each part, in turn. -/
def ssWalkBody (nm : ℕ) : Stmt :=
  .seq (ssQuery nm (.bin .sub (.reg 12) (.const 1)) 12)
    (.cond (.bin .eq (.reg 12) (.reg 9)) (.assign 14 (.const 0))
      (.seq (ssQuery nm (.bin .sub (.reg 13) (.const 1)) 13)
        (.cond (.bin .eq (.reg 13) (.reg 10))
          (.seq (.assign 11 (.const 1)) (.assign 14 (.const 0))) .nop)))

/-- Copy the list at register `7` (its length word and its entries) to register `8`. -/
def ssCopy : Stmt :=
  forRange 19 (.const 0) (.bin .add (.reg 18) (.const 1))
    (.store (.bin .add (.reg 8) (.reg 19)) (.load (.bin .add (.reg 7) (.reg 19))))

/-- List the chosen part, copy the list, finish the record and return the new heap. -/
def ssTail (lm : ℕ) : Stmt :=
  .seq (.assign 16 (.reg 1))
    (.seq (.cond (.reg 11) (.assign 16 (.reg 2)) .nop)
      (.seq (.call 8 lm [.reg 0, .reg 16, .reg 7])
        (.seq (.assign 18 (.load (.reg 7)))
          (.seq ssCopy
            (.seq (.store (.bin .add (.reg 6) (.const 2)) (.reg 11))
              (.seq (.store (.bin .add (.reg 6) (.const 3)) (.reg 8))
                (.ret (.bin .add (.bin .add (.reg 8) (.reg 18)) (.const 1)))))))))

/-- **The helper `outSmallSide`** `[tourH, r₁, r₂, v, v', last, h]`, for the tour procedures
`nm` (`nextMarked`), `fm` (`firstMarked`) and `lm` (`listMarked`). -/
def outSmallSideBody (nm fm lm : ℕ) : Stmt :=
  .seq ssHead
    (.seq (ssQuery fm (.reg 1) 9)
      (.seq (ssQuery fm (.reg 2) 10)
        (.seq ssInit
          (.seq (.loop (.reg 14) (ssWalkBody nm)) (ssTail lm)))))

/-- A tour query moves the heap pointer, writes its answer in `dst`, and keeps the other
registers below `7`, and from `9` on except `dst`. -/
theorem ssQuery_runs {w : ℕ} {p : Program} {ω : ℕ → Bool} {f dst : ℕ} {argE : Expr}
    {st : State} {x : ℕ} {body : Stmt} {o₁ : Outcome} {st₁ : State} {c₁ : ℕ}
    (hdst7 : dst ≠ 7) (hdst8 : dst ≠ 8)
    (harg : argE.eval w st = some x) (hproc : p.procs[f]? = some body)
    (hrun : Runs w p ω body (startState [st.regs 0, x, st.regs 7] st.mem st.pos) o₁ st₁ c₁) :
    ∃ st' : State, Runs w p ω (ssQuery f argE dst) st .normal st' (c₁ + argE.size + 10) ∧
      st'.mem = st₁.mem ∧ st'.pos = st₁.pos ∧ st'.regs 7 = o₁.value ∧
      st'.regs dst = st₁.mem (st.regs 7) ∧
      ∀ r, r ≠ 7 → r ≠ 8 → r ≠ dst → st'.regs r = st.regs r := by
  have hargs : evalArgs w st [.reg 0, argE, .reg 7] = some [st.regs 0, x, st.regs 7] :=
    evalArgs_cons (Expr.eval_reg w 0 st) (evalArgs_cons harg
      (evalArgs_cons (Expr.eval_reg w 7 st) (evalArgs_nil w st)))
  have hcall := runs_call_of (r := 8) (ω := ω) hargs hproc hrun
  set st₂ : State := { st₁ with regs := Function.update st.regs 8 o₁.value } with hst₂
  have h27 : st₂.regs 7 = st.regs 7 := by simp [hst₂]
  have hld : (Expr.load (.reg 7)).eval w st₂ = some (st₁.mem (st.regs 7)) :=
    Expr.eval_load_of_eq (Expr.eval_reg_of_eq h27) rfl
  have ha1 := runs_assign_of (p := p) (ω := ω) (r := dst) hld
  set st₃ : State := { st₂ with regs := Function.update st₂.regs dst (st₁.mem (st.regs 7)) }
    with hst₃
  have h38 : st₃.regs 8 = o₁.value := by simp [hst₃, hst₂, Function.update_of_ne hdst8.symm]
  have ha2 := runs_assign_of (w := w) (p := p) (ω := ω) (r := 7) (Expr.eval_reg_of_eq h38)
  have hrun' := runs_seq_normal hcall (runs_seq_normal ha1 ha2)
  refine ⟨{ st₃ with regs := Function.update st₃.regs 7 o₁.value }, ?_, rfl, rfl,
    by simp, ?_, ?_⟩
  · have hc : argsSize [.reg 0, argE, .reg 7] + c₁ + 1 + ((Expr.load (.reg 7)).size + 1 +
        ((Expr.reg 8).size + 1) + 1) + 1 = c₁ + argE.size + 10 := by
      simp only [argsSize, Expr.size_reg, Expr.size_load]; omega
    exact hc ▸ hrun'
  · show Function.update st₃.regs 7 o₁.value dst = _
    rw [Function.update_of_ne hdst7, hst₃]
    simp
  · intro r h7 h8 hd
    simp [hst₃, hst₂, Function.update_of_ne h7, Function.update_of_ne hd, Function.update_of_ne h8]

/-! ## The frame of the helper -/

section Frame

variable {S : OutTourSpec} {w vCap eCap : ℕ} {p : Program} {nm sm fm lm : ℕ}

/-- The frame that the helper keeps at heap `cur`, for the concrete tour state `tx` in memory
`mem`, from the start state `tx₀` in memory `mem₀`: the tour holds `s`, memory is zero from
`cur` on, the tour takes only old cells or cells between the record and `cur`, the cells below
`h` outside the old tour are unchanged (except the link word of `last`), and the record holds
`v`, `v'` and a zero link. -/
def SSFrame (T : OutTourAt S w vCap eCap p nm sm fm lm) (tourH last h v v' : ℕ) (s : OutTourAbs)
    (tx₀ : T.rep.τ) (mem₀ : ℕ → ℕ) (cur : ℕ) (tx : T.rep.τ) (mem : ℕ → ℕ) : Prop :=
  T.rep.rep tourH s tx mem ∧ ZeroFrom mem cur ∧ h + 5 ≤ cur ∧
    (∀ a, T.rep.foot tourH tx a → T.rep.foot tourH tx₀ a ∨ (h + 5 ≤ a ∧ a < cur)) ∧
    (∀ a < h, ¬ T.rep.foot tourH tx₀ a → (last = 0 ∨ a ≠ last + 4) → mem a = mem₀ a) ∧
    mem h = v ∧ mem (h + 1) = v' ∧ mem (h + 4) = 0 ∧ (last ≠ 0 → mem (last + 4) = h)

/-- A tour call at the heap pointer `cur` that respects memory keeps the frame. -/
theorem SSFrame.respects {T : OutTourAt S w vCap eCap p nm sm fm lm} {tourH last h v v' : ℕ}
    {s : OutTourAbs} {tx₀ : T.rep.τ} {mem₀ : ℕ → ℕ} {cur cur' sp : ℕ} {tx tx' : T.rep.τ}
    {mem mem' : ℕ → ℕ} (hfoot₀ : ∀ a, T.rep.foot tourH tx₀ a → a < h)
    (hlast : last = 0 ∨ (last + 4 < h ∧ ¬ T.rep.foot tourH tx₀ (last + 4)))
    (hF : SSFrame T tourH last h v v' s tx₀ mem₀ cur tx mem)
    (hrep' : T.rep.rep tourH s tx' mem')
    (hresp : T.rep.Respects (T.rep.foot tourH tx) cur sp mem cur' tourH tx' mem') :
    SSFrame T tourH last h v v' s tx₀ mem₀ cur' tx' mem' := by
  obtain ⟨-, hz, hcur, hft, hfr, hv, hv', h4, hl⟩ := hF
  obtain ⟨hle, -, hz', hkeep, hft'⟩ := hresp
  -- a cell below `cur` outside the old tour and outside the cells it took keeps its word
  have hkeep' : ∀ a, a < h + 5 → ¬ T.rep.foot tourH tx₀ a → mem' a = mem a := by
    intro a ha hn
    refine hkeep a (by omega) fun hf => ?_
    rcases hft a hf with hf | ⟨h1, -⟩
    · exact hn hf
    · omega
  have hnot : ∀ a, h ≤ a → ¬ T.rep.foot tourH tx₀ a := fun a ha hf => by
    have := hfoot₀ a hf; omega
  refine ⟨hrep', hz', by omega, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rcases hft' a ha with ha | ⟨h1, h2⟩
    · rcases hft a ha with ha | ⟨h1, h2⟩
      · exact Or.inl ha
      · exact Or.inr ⟨h1, by omega⟩
    · exact Or.inr ⟨by omega, h2⟩
  · intro a ha hn hl'
    rw [hkeep' a (by omega) hn]; exact hfr a ha hn hl'
  · rw [hkeep' h (by omega) (hnot h le_rfl)]; exact hv
  · rw [hkeep' (h + 1) (by omega) (hnot _ (by omega))]; exact hv'
  · rw [hkeep' (h + 4) (by omega) (hnot _ (by omega))]; exact h4
  · intro hl0
    rcases hlast with hl1 | ⟨hl1, hl2⟩
    · exact absurd hl1 hl0
    · rw [hkeep' (last + 4) (by omega) hl2]; exact hl hl0

end Frame

end MinCostFlow.SparseCore.Program
