module

public import MinCostFlow.LinkCut.Gen.Steps

/-!
# Helpers for the generic tree programs

Tree programs get the address `nb` of the record of node `0` in register `0`. They first load
the record width into register `20` (`strideLoad`), and then compute the address of the record
of a node with `recAddr`. So the program text does not depend on the layout.

`HeapOk` is the shape of memory every tree run theorem assumes: all records lie below the heap
pointer, there is room for the payload scratch, and memory from the heap pointer on is zero.

`runs_seq_callBody_le` runs a call to a tree procedure from a run theorem of its body (rather
than from a contract), in the forward style of `WordRAM.Logic`.

`PtrOk cap st` says that the four pointers of nodes `0 .. cap` are at most `cap`. The tree
programs need it to compute record addresses; every tree operation keeps it.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-- The address of the record of the node in register `rx`, with `nb` in register `0` and the
record width in register `20`. -/
abbrev recAddr (rx : ℕ) : Expr :=
  .bin .add (.reg 0) (.bin .mul (.reg 20) (.reg rx))

/-- The first statement of a tree procedure: load the record width into register `20`. The
width is the first word of the value block of node `0` (`NodeLayout.val_hdr`). -/
abbrev strideLoad : Stmt := .assign 20 (.load (.bin .add (.reg 0) (.const 6)))

/-- Records end below the heap pointer: the shape every tree run theorem assumes. -/
structure HeapOk (Lay : NodeLayout α σ τ) (w nb cap heap space : ℕ) (mem : ℕ → ℕ) : Prop where
  rec_le : Lay.nodeAddr nb (cap + 1) ≤ heap
  room : heap + space < 2 ^ w
  zero : ZeroFrom mem heap
  wide : 16 ≤ 2 ^ w

theorem HeapOk.addr_lt {Lay : NodeLayout α σ τ} {w nb cap heap space : ℕ} {mem : ℕ → ℕ}
    (h : HeapOk Lay w nb cap heap space mem) {x : ℕ} (hx : x ≤ cap) :
    Lay.nodeAddr nb x + Lay.nodeStride ≤ heap := by
  have := h.rec_le
  unfold nodeAddr at *
  have : Lay.nodeStride * x + Lay.nodeStride ≤ Lay.nodeStride * (cap + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- A cell of a record of a node `≤ cap` is in the records. -/
theorem inRecords_of_rec {Lay : NodeLayout α σ τ} {nb cap x i : ℕ} (hx : x ≤ cap)
    (hi : i < Lay.nodeStride) : Lay.InRecords nb cap (Lay.nodeAddr nb x + i) := by
  refine ⟨by unfold nodeAddr; omega, ?_⟩
  unfold nodeAddr
  have : Lay.nodeStride * x + Lay.nodeStride ≤ Lay.nodeStride * (cap + 1) := by
    rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
  omega

/-- Evaluating `recAddr`. -/
theorem eval_recAddr {w nb x rx : ℕ} {Lay : NodeLayout α σ τ} {st : State}
    (h0 : st.regs 0 = nb) (hx : st.regs rx = x) (hS : st.regs 20 = Lay.nodeStride)
    (hlt : Lay.nodeAddr nb x < 2 ^ w) :
    (recAddr rx).eval w st = some (Lay.nodeAddr nb x) := by
  have hmul : Lay.nodeStride * x < 2 ^ w := by unfold nodeAddr at hlt; omega
  exact Expr.eval_add (Expr.eval_reg_of_eq h0)
    (Expr.eval_mul (Expr.eval_reg_of_eq hS) (Expr.eval_reg_of_eq hx) hmul) hlt

/-- Loading the word at `nb + k` into register `r`, followed by `s`. -/
theorem runs_seq_load0_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r k : ℕ}
    {s : Stmt} {st : State} {nb v c T : ℕ} {Q : Outcome → State → Prop}
    (h0 : st.regs 0 = nb) (hm : st.mem (nb + k) = v) (hw : nb + k < 2 ^ w)
    (hrest : ∃ o st' cc, Runs w p ω s
      { st with regs := Function.update st.regs r v } o st' cc ∧
      Q o st' ∧ (c + 6) + cc ≤ T) :
    ∃ o st' cc, Runs w p ω (.seq (.assign r (.load (.bin .add (.reg 0) (.const k)))) s) st o st'
      cc ∧ Q o st' ∧ c + cc ≤ T :=
  runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h0)
    (Expr.eval_const (by omega)) hw) hm) hrest

/-- The run of `strideLoad`, followed by `s`. -/
theorem runs_seq_strideLoad_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {Lay : NodeLayout α σ τ}
    {s : Stmt} {st : State} {nb k T : ℕ} {Q : Outcome → State → Prop}
    (h0 : st.regs 0 = nb) (hm : st.mem (nb + 6) = Lay.nodeStride) (hw : nb + 6 < 2 ^ w)
    (hrest : ∃ o st' c, Runs w p ω s
      { st with regs := Function.update st.regs 20 Lay.nodeStride } o st' c ∧
      Q o st' ∧ (k + 6) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq strideLoad s) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_assign_le (Expr.eval_load_of_eq (Expr.eval_add (Expr.eval_reg_of_eq h0)
    (Expr.eval_const (by omega)) hw) hm) hrest

theorem HeapOk.stride_lt {Lay : NodeLayout α σ τ} {w nb cap heap space : ℕ} {mem : ℕ → ℕ}
    (h : HeapOk Lay w nb cap heap space mem) : Lay.nodeStride < 2 ^ w := by
  have h1 := h.addr_lt (Nat.zero_le cap)
  have h2 := h.room
  omega

theorem HeapOk.nb6 {Lay : NodeLayout α σ τ} {w nb cap heap space : ℕ} {mem : ℕ → ℕ}
    (h : HeapOk Lay w nb cap heap space mem) : nb + 6 < 2 ^ w := by
  have h1 := h.addr_lt (Nat.zero_le cap)
  have h2 := h.room
  have := Lay.stride_pos
  unfold nodeAddr at h1
  omega

theorem HeapOk.nb9 {Lay : NodeLayout α σ τ} {w nb cap heap space : ℕ} {mem : ℕ → ℕ}
    (h : HeapOk Lay w nb cap heap space mem) : nb + 9 ≤ heap := by
  have h1 := h.addr_lt (Nat.zero_le cap)
  have := Lay.stride_nine
  unfold nodeAddr at h1
  omega

@[simp] theorem recAddr_size (rx : ℕ) : (recAddr rx).size = 5 := rfl

/-- A call to procedure `f` whose body has a run from the callee's start state, followed by `s`.
The property `R` of the callee's run (its outcome value, final state and cost) is all the rest
of the run may use. -/
theorem runs_seq_callBody_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {r f : ℕ}
    {args : List Expr} {body s : Stmt} {st : State} {vs : List ℕ} {k T : ℕ}
    {Q : Outcome → State → Prop} {R : ℕ → State → ℕ → Prop}
    (hproc : p.procs[f]? = some body) (hargs : evalArgs w st args = some vs)
    (hbody : ∃ o₁ st₁ c₁, Runs w p ω body (startState vs st.mem st.pos) o₁ st₁ c₁ ∧
      R o₁.value st₁ c₁)
    (hrest : ∀ v st₁ c₁, R v st₁ c₁ → ∃ o st' c,
      Runs w p ω s { st₁ with regs := Function.update st.regs r v } o st' c ∧ Q o st' ∧
        (k + argsSize args + c₁ + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r f args) s) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o₁, st₁, c₁, hr₁, hR⟩ := hbody
  obtain ⟨o, st', c, hr, hq, hc⟩ := hrest o₁.value st₁ c₁ hR
  refine ⟨o, st', (argsSize args + c₁ + 1) + c + 1, ?_, hq, by omega⟩
  exact runs_seq_normal (runs_call_iff.mpr ⟨vs, body, o₁, st₁, c₁, hargs, hproc, hr₁, rfl, rfl,
    rfl⟩) hr

/-- A statement with a known run, followed by `t`. -/
theorem runs_seq_run_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {s t : Stmt} {st st₁ : State}
    {c₁ k T : ℕ} {Q : Outcome → State → Prop} (h₁ : Runs w p ω s st .normal st₁ c₁)
    (hrest : ∃ o st' c, Runs w p ω t st₁ o st' c ∧ Q o st' ∧ (k + c₁ + 1) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq s t) st o st' c ∧ Q o st' ∧ k + c ≤ T := by
  obtain ⟨o, st', c, hr, hq, hc⟩ := hrest
  exact ⟨o, st', c₁ + c + 1, runs_seq_normal h₁ hr, hq, by omega⟩

/-- A payload call on the record of `x`: if below the heap pointer only the payload cells of
that record change, memory from the heap pointer on is zero before and after, and the payload
blocks of `x` now hold `v`, `s`, `t`, then the records hold the state with those payload fields
of `x` replaced. -/
theorem NodesAt.payload {Lay : NodeLayout α σ τ} {mem mem' : ℕ → ℕ} {nb cap x heap : ℕ}
    {st : SplayState α σ τ} {v : α} {s : σ} {t : τ}
    (h : Lay.NodesAt mem nb cap st) (hx : x ≤ cap) (hz : ZeroFrom mem heap)
    (hz' : ZeroFrom mem' heap)
    (hctrl : ∀ y < heap, ¬ Lay.PayCell (Lay.nodeAddr nb x) y → mem' y = mem y)
    (hv : Lay.ValAt mem' (Lay.nodeAddr nb x + OFF_VAL) v)
    (hs : Lay.SumAt mem' (Lay.nodeAddr nb x + Lay.offSum) s)
    (ht : Lay.TagAt mem' (Lay.nodeAddr nb x + Lay.offTag) t) :
    Lay.NodesAt mem' nb cap (st.updateNode x fun nd => { nd with val := v, sum := s, tag := t }) := by
  have hS6 := Lay.stride_pos
  have hsame : ∀ y, ¬ Lay.PayCell (Lay.nodeAddr nb x) y → mem' y = mem y := fun y hy => by
    by_cases hyh : y < heap
    · exact hctrl y hyh hy
    · rw [hz y (by omega), hz' y (by omega)]
  refine h.update Lay hx ?_ fun a ha => hsame a fun hc => by
    unfold PayCell at hc
    exact ha (a - Lay.nodeAddr nb x) (by omega) (by omega)
  obtain ⟨h0, h1, h2, h3, h4, h5, -, -, -⟩ := h x hx
  have hk : ∀ k < 6, mem' (Lay.nodeAddr nb x + k) = mem (Lay.nodeAddr nb x + k) := fun k hk =>
    hsame _ fun hc => by unfold PayCell OFF_VAL at hc; omega
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, hv, hs, ht⟩
  · rw [hk _ (by decide)]; exact h0
  · rw [hk _ (by decide)]; exact h1
  · rw [hk _ (by decide)]; exact h2
  · rw [hk _ (by decide)]; exact h3
  · rw [hk _ (by decide)]; exact h4
  · rw [hk _ (by decide)]; exact h5

/-- The frame of a payload call on the record of `x`. -/
theorem TreeFrame.of_payload {Lay : NodeLayout α σ τ} {mem mem' : ℕ → ℕ} {nb cap x heap : ℕ}
    (hx : x ≤ cap) (hz' : ZeroFrom mem' heap)
    (hctrl : ∀ y < heap, ¬ Lay.PayCell (Lay.nodeAddr nb x) y → mem' y = mem y) :
    TreeFrame Lay nb cap heap mem mem' := by
  refine ⟨hz', fun a ha hnr => hctrl a ha fun hc => hnr ?_⟩
  unfold PayCell at hc
  have := inRecords_of_rec (Lay := Lay) (nb := nb) hx (i := a - Lay.nodeAddr nb x) (by omega)
  rwa [show Lay.nodeAddr nb x + (a - Lay.nodeAddr nb x) = a by omega] at this

theorem HeapOk.mono {Lay : NodeLayout α σ τ} {w nb cap heap space space' : ℕ} {mem : ℕ → ℕ}
    (h : HeapOk Lay w nb cap heap space mem) (hle : space' ≤ space) :
    HeapOk Lay w nb cap heap space' mem :=
  ⟨h.rec_le, by have := h.room; omega, h.zero, h.wide⟩

theorem splayState_ext {a b : SplayState α σ τ} (h : ∀ y, a.nodes y = b.nodes y) : a = b := by
  cases a; cases b; congr; funext y; exact h y

/-- The frame of one write into a control word of the record of `x`. -/
theorem TreeFrame.of_ctrl {Lay : NodeLayout α σ τ} {mem : ℕ → ℕ} {nb cap x heap off v : ℕ}
    (hx : x ≤ cap) (hoff : off < 6) (hrec : Lay.nodeAddr nb x + Lay.nodeStride ≤ heap)
    (hz : ZeroFrom mem heap) :
    TreeFrame Lay nb cap heap mem (Function.update mem (Lay.nodeAddr nb x + off) v) := by
  have := Lay.stride_pos
  refine ⟨fun a ha => ?_, fun a _ hnr => Function.update_of_ne ?_ _ _⟩
  · rw [Function.update_of_ne (by omega)]; exact hz a ha
  · rintro rfl; exact hnr (inRecords_of_rec hx (by omega))

/-- A store followed by `s`, with the new memory given a name. -/
theorem runs_seq_store_named_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {a e : Expr} {s : Stmt}
    {st : State} {x v k T : ℕ} {Q : Outcome → State → Prop}
    (ha : a.eval w st = some x) (he : e.eval w st = some v)
    (hrest : ∀ M, M = Function.update st.mem x v → ∃ o st' c,
      Runs w p ω s { st with mem := M } o st' c ∧ Q o st' ∧ (k + a.size + e.size + 2) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.store a e) s) st o st' c ∧ Q o st' ∧ k + c ≤ T :=
  runs_seq_store_le ha he (hrest _ rfl)

/-- A store done only if `e` is nonzero, followed by `s`, with the new memory given a name. -/
theorem runs_seq_condStore_named_le {w : ℕ} {p : Program} {ω : ℕ → Bool} {e a e₂ : Expr}
    {s : Stmt} {st : State} {c x v k T : ℕ} {Q : Outcome → State → Prop}
    (he : e.eval w st = some c) (ha : c ≠ 0 → a.eval w st = some x)
    (he₂ : c ≠ 0 → e₂.eval w st = some v)
    (hrest : ∀ M, M = (if c = 0 then st.mem else Function.update st.mem x v) → ∃ o st' cc,
      Runs w p ω s { st with mem := M } o st' cc ∧ Q o st' ∧
        (k + e.size + a.size + e₂.size + 4) + cc ≤ T) :
    ∃ o st' cc, Runs w p ω (.seq (.cond e (.store a e₂) .nop) s) st o st' cc ∧ Q o st' ∧
      k + cc ≤ T := by
  refine runs_seq_cond_le he (fun hc => ?_) (fun hc => ?_)
  · refine runs_seq_store_le (ha hc) (he₂ hc) ?_
    obtain ⟨o, st', cc, hr, hq, hcc⟩ := hrest _ rfl
    rw [if_neg hc] at hr
    exact ⟨o, st', cc, hr, hq, by omega⟩
  · refine runs_seq_nop_le ?_
    obtain ⟨o, st', cc, hr, hq, hcc⟩ := hrest _ rfl
    rw [if_pos hc] at hr
    exact ⟨o, st', cc, hr, hq, by omega⟩

/-- The four pointers of nodes `0 .. cap` are at most `cap`. -/
def PtrOk (cap : ℕ) (st : SplayState α σ τ) : Prop :=
  ∀ x ≤ cap, (st.nodes x).left ≤ cap ∧ (st.nodes x).right ≤ cap ∧ (st.nodes x).par ≤ cap ∧
    (st.nodes x).ppar ≤ cap

end MinCostFlow.LinkCut.Gen
