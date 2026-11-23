module

public import MinCostFlow.LinkCut.Gen.Index
public import MinCostFlow.LinkCut.Gen.Splay

/-!
# Splicing auxiliary trees as programs

`detachRightBody`, `attachRightBody` and `detachRootChildrenBody` are the machine versions of
`SplayState.detachRight`, `SplayState.attachRight` and `SplayState.detachRootChildren`. Each one
does the pointer writes of the model in the same order and then calls `pull` on the root. The
states of the model before that `pull` are `detachRightMid`, `attachRightMid` and
`detachChildrenMid`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-- One write of a control word of the record of `y`, with its effect on the records and the
frame. -/
theorem NodesAt.ctrl {Lay : NodeLayout α σ τ} {mem M : ℕ → ℕ} {nb cap heap y off v : ℕ}
    {st st' : SplayState α σ τ} (hN : Lay.NodesAt M nb cap st)
    (hF : TreeFrame Lay nb cap heap mem M) (hy : y ≤ cap) (hoff : off < 6)
    (hA : Lay.nodeAddr nb y + Lay.nodeStride ≤ heap)
    (hset : Lay.NodesAt M nb cap st → Lay.NodesAt (Function.update M (Lay.nodeAddr nb y + off) v)
      nb cap st') :
    Lay.NodesAt (Function.update M (Lay.nodeAddr nb y + off) v) nb cap st' ∧
      TreeFrame Lay nb cap heap mem (Function.update M (Lay.nodeAddr nb y + off) v) :=
  ⟨hset hN, hF.trans (TreeFrame.of_ctrl hy hoff hA hF.1)⟩

/-- A write of a control word of the record of `y` done only when `y ≠ 0`. -/
theorem NodesAt.condCtrl {Lay : NodeLayout α σ τ} {mem M : ℕ → ℕ} {nb cap heap y off v : ℕ}
    {st st' : SplayState α σ τ} (hN : Lay.NodesAt M nb cap st)
    (hF : TreeFrame Lay nb cap heap mem M) (hy : y ≤ cap) (hoff : off < 6)
    (hA : Lay.nodeAddr nb y + Lay.nodeStride ≤ heap)
    (hset : Lay.NodesAt M nb cap st → Lay.NodesAt (Function.update M (Lay.nodeAddr nb y + off) v)
      nb cap st') :
    Lay.NodesAt (if y = 0 then M else Function.update M (Lay.nodeAddr nb y + off) v) nb cap
        (if y = 0 then st else st') ∧
      TreeFrame Lay nb cap heap mem
        (if y = 0 then M else Function.update M (Lay.nodeAddr nb y + off) v) := by
  split_ifs
  · exact ⟨hN, hF⟩
  · exact NodesAt.ctrl hN hF hy hoff hA hset

/-! ### `detachRight` -/

/-- The pointer writes of `SplayState.detachRight` when `x` and its right child are not `0`. -/
def detachRightMid (st : SplayState α σ τ) (x : ℕ) : SplayState α σ τ :=
  ((st.setPar (st.nodes x).right 0).setPpar (st.nodes x).right x).setRight x 0

theorem detachRight_eq {P : LctPayload α σ τ} {st : SplayState α σ τ} {x : ℕ} (hx : x ≠ 0)
    (hr : (st.nodes x).right ≠ 0) :
    SplayState.detachRight P st x = SplayState.pull P (detachRightMid st x) x := by
  simp only [SplayState.detachRight, detachRightMid, hx, hr, if_false]

theorem PtrOk.detachRightMid {cap x : ℕ} {st : SplayState α σ τ} (h : PtrOk cap st)
    (hx : x ≤ cap) : PtrOk cap (Gen.detachRightMid st x) := by
  have hr := (h x hx).2.1
  unfold Gen.detachRightMid
  exact ((h.setPar hr (Nat.zero_le _)).setPpar hr hx).setRight hx (Nat.zero_le _)

theorem PtrOk.detachRight {cap x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.detachRight P st x) := by
  by_cases hx0 : x = 0
  · simpa [SplayState.detachRight, hx0] using h
  by_cases hr0 : (st.nodes x).right = 0
  · simpa [SplayState.detachRight, hx0, hr0] using h
  rw [detachRight_eq hx0 hr0]
  exact (h.detachRightMid hx).pull hx

/-- `detachRight` on `[nb, x, heap]`. It also notes `x`, and the cut-off child, in the index
(`Gen/Index.lean`): both may be new roots, or roots with a new summary. -/
def detachRightBody (pullProc noteProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.call 6 noteProc [.reg 0, .reg 1] ;;
     .assign 3 (recAddr 1) ;;
     .assign 4 (.load (.bin .add (.reg 3) (.const 1))) ;;
     .cond (.bin .eq (.reg 4) (.const 0)) (.ret (.const 0))
       (.assign 5 (recAddr 4) ;;
        .store (.bin .add (.reg 5) (.const 2)) (.const 0) ;;
        .store (.bin .add (.reg 5) (.const 3)) (.reg 1) ;;
        .store (.bin .add (.reg 3) (.const 1)) (.const 0) ;;
        .call 6 pullProc [.reg 0, .reg 1, .reg 2] ;;
        .call 6 noteProc [.reg 0, .reg 4] ;;
        .ret (.const 0)))

theorem detachRightBody_noRand (pullProc noteProc : ℕ) :
    (detachRightBody pullProc noteProc).NoRand := by
  simp [detachRightBody, recAddr, Stmt.NoRand]

/-- The summary that `detachRight P st x` computes is representable. -/
def DetachRightOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : SplayState α σ τ)
    (x : ℕ) : Prop :=
  x ≠ 0 → (st.nodes x).right ≠ 0 → ok.sumOk (pullSum P (detachRightMid st x) x)

/-- The nodes `detachRight` notes: `x` (if not `0`), then its right child (if not `0`). -/
def drNotes (st : SplayState α σ τ) (x : ℕ) (S : List ℕ) : List ℕ :=
  if x = 0 then S
  else if (st.nodes x).right = 0 then noteList S x
  else noteList (noteList S x) (st.nodes x).right

/-- Running a note from a state whose records hold `st`: the records still hold `st`, and the
index holds the stack with `x` pushed. -/
theorem runs_seq_note {w nb cap heap x : ℕ} {Lay : NodeLayout α σ τ} {p : Program}
    {ω : ℕ → Bool} {noteProc r : ℕ} {e₀ e₁ : Expr} {s : Stmt} {st₀ : State} {k T : ℕ}
    {Q : Outcome → State → Prop} {mem₀ : ℕ → ℕ} {S S₀ : List ℕ} {sp : SplayState α σ τ}
    (hnote : p.procs[noteProc]? = some noteBody)
    (h0 : e₀.eval w st₀ = some nb) (h1 : e₁.eval w st₀ = some x)
    (hx : x ≤ cap) (hnb : 2 * cap + 3 ≤ nb) (hnh : nb ≤ heap) (hw : nb < 2 ^ w)
    (hN : Lay.NodesAt st₀.mem nb cap sp) (hF : IdxFrame Lay nb cap heap mem₀ st₀.mem S₀)
    (hS : S₀ = S)
    (hrest : ∀ v (st₁ : State), Lay.NodesAt st₁.mem nb cap sp →
      IdxFrame Lay nb cap heap mem₀ st₁.mem (noteList S x) → ∃ o st' c,
      Runs w p ω s { st₁ with regs := Function.update st₀.regs r v } o st' c ∧ Q o st' ∧
        (k + e₀.size + e₁.size + 62) + c ≤ T) :
    ∃ o st' c, Runs w p ω (.seq (.call r noteProc [e₀, e₁]) s) st₀ o st' c ∧ Q o st' ∧
      k + c ≤ T := by
  subst hS
  refine runs_seq_callBody_le (vs := [nb, x]) hnote (by simp [evalArgs, h0, h1])
    (R := fun _ m c => Lay.NodesAt m.mem nb cap sp ∧
      IdxFrame Lay nb cap heap mem₀ m.mem (noteList S₀ x) ∧ c ≤ 60) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hI', hk⟩, hc⟩ := noteBody_runs (p := p) ω (pos := st₀.pos) hF.2 hx
      hnb hw
    refine ⟨o, st', c, hr, hN.congr Lay fun a ha => hk a fun hi => ?_,
      ⟨hF.1.trans (TreeFrameN.of_note hF.1.1 hnh hk), hI'⟩, by omega⟩
    exact not_inRecords_of_inIndex hi ha
  rintro v st₁ c₁ ⟨hN₁, hF₁, hc₁⟩
  obtain ⟨o, st', c, hr, hq, hc⟩ := hrest v st₁ hN₁ hF₁
  exact ⟨o, st', c, hr, hq, by simp only [argsSize_cons, argsSize_nil] at *; omega⟩

/-- The run of `detachRightBody`. -/
theorem detachRightBody_runs {w nb cap x heap pos pullProc noteProc : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (hpull : p.procs[pullProc]? = some (pullBody S.pull))
    (hnote : p.procs[noteProc]? = some noteBody)
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ} {I : List ℕ}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap S.space mem) (hok : DetachRightOk ok P st x)
    (hnb : 2 * cap + 3 ≤ nb) (hI : IdxAt mem nb cap I) :
    ∃ o st' c, Runs w p ω (detachRightBody pullProc noteProc)
        (startState [nb, x, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.detachRight P st x) ∧
        IdxFrame Lay nb cap heap mem st'.mem (drNotes st x I)) ∧ 0 + c ≤ S.cost + 400 := by
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS := hheap.stride_lt
  have hS6 := Lay.stride_pos
  have hrec := hheap.rec_le
  have hlt : ∀ y ≤ cap, nb + Lay.nodeStride * y + Lay.nodeStride ≤ heap := fun y hy => by
    have := hheap.addr_lt hy; unfold nodeAddr at this; exact this
  have hnh : nb ≤ heap := by have := hlt 0 (Nat.zero_le _); omega
  obtain ⟨-, hrc, -, -⟩ := hptr x hx
  set r := (st.nodes x).right with hr
  have hAx := hlt x hx
  have hAr := hlt r hrc
  unfold detachRightBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [SplayState.detachRight] using hnodes,
        IdxFrame.refl hheap.zero (by simpa [drNotes] using hI)⟩
    · wram_cost
  have hx0 : x ≠ 0 := hcond
  refine runs_seq_note (S := I) hnote (by eval_expr) (by eval_expr) hx hnb hnh (by omega)
    hnodes (IdxFrame.refl hheap.zero hI) rfl fun v₁ m₁ hN₁ hF₁ => ?_
  have hm1 : m₁.mem (nb + Lay.nodeStride * x + 1) = r := (hN₁ x hx).2.1
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hm1]
  wram_step
  · have hr0 : r = 0 := hcond
    wram_step
    · refine ⟨by simpa [SplayState.detachRight, hx0, ← hr, hr0] using hN₁, ?_⟩
      simpa [drNotes, hx0, ← hr, hr0] using hF₁
    · wram_cost
  have hr0 : r ≠ 0 := hcond
  wram_step; try dsimp only
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₁ hM₁ => ?_
  have h₁ : Lay.NodesAt M₁ nb cap (st.setPar r 0) ∧ TreeFrame Lay nb cap heap m₁.mem M₁ := by
    rw [hM₁]; exact NodesAt.ctrl hN₁ (TreeFrame.refl hF₁.1.1) hrc (by decide) hAr
      (fun h => h.setPar Lay hrc)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₂ hM₂ => ?_
  have h₂ : Lay.NodesAt M₂ nb cap ((st.setPar r 0).setPpar r x) ∧
      TreeFrame Lay nb cap heap m₁.mem M₂ := by
    rw [hM₂]; exact NodesAt.ctrl h₁.1 h₁.2 hrc (by decide) hAr (fun h => h.setPpar Lay hrc)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₃ hM₃ => ?_
  have h₃ : Lay.NodesAt M₃ nb cap (detachRightMid st x) ∧ TreeFrame Lay nb cap heap m₁.mem M₃ := by
    rw [hM₃]; exact NodesAt.ctrl h₂.1 h₂.2 hx (by decide) hAx (fun h => h.setRight Lay hx)
  refine runs_seq_callBody_le hpull (by eval_expr)
    (R := fun _ st₄ c₄ => Lay.NodesAt st₄.mem nb cap (SplayState.detachRight P st x) ∧
      TreeFrame Lay nb cap heap m₁.mem st₄.mem ∧ c₄ ≤ S.cost + 150) ?_ ?_
  · obtain ⟨o, st', c, hrun, ⟨hn, hf⟩, hc⟩ := pullBody_runs S ω h₃.1 (hptr.detachRightMid hx) hx
      ⟨hrec, hroom, h₃.2.1, hwide⟩ (fun _ => hok hx0 hr0)
    refine ⟨o, st', c, hrun, ?_, h₃.2.trans hf, by omega⟩
    rw [detachRight_eq hx0 hr0]; exact hn
  rintro - st₄ c₄ ⟨hN₄, hF₄, hc₄⟩
  have hF₄' := hF₁.trans_tree hnb hnh hF₄
  refine runs_seq_note (S := noteList I x) hnote (by eval_expr) (by eval_expr) hrc hnb hnh
    (by omega) hN₄ hF₄' rfl fun v₅ m₅ hN₅ hF₅ => ?_
  wram_step
  · refine ⟨hN₅, ?_⟩
    simpa [drNotes, hx0, ← hr, hr0] using hF₅
  · wram_cost

/-! ### `attachRight` -/

/-- The pointer writes of `SplayState.attachRight` when `u ≠ 0`. -/
def attachRightMid (st : SplayState α σ τ) (u x : ℕ) : SplayState α σ τ :=
  if x = 0 then st.setRight u x else ((st.setRight u x).setPar x u).setPpar x 0

theorem attachRight_eq {P : LctPayload α σ τ} {st : SplayState α σ τ} {u x : ℕ} (hu : u ≠ 0) :
    SplayState.attachRight P st u x = SplayState.pull P (attachRightMid st u x) u := by
  simp only [SplayState.attachRight, attachRightMid, hu, if_false]

theorem PtrOk.attachRightMid {cap u x : ℕ} {st : SplayState α σ τ} (h : PtrOk cap st)
    (hu : u ≤ cap) (hx : x ≤ cap) : PtrOk cap (Gen.attachRightMid st u x) := by
  unfold Gen.attachRightMid
  split_ifs
  · exact h.setRight hu hx
  · exact ((h.setRight hu hx).setPar hx hu).setPpar hx (Nat.zero_le _)

theorem PtrOk.attachRight {cap u x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hu : u ≤ cap) (hx : x ≤ cap) :
    PtrOk cap (SplayState.attachRight P st u x) := by
  by_cases hu0 : u = 0
  · simpa [SplayState.attachRight, hu0] using h
  rw [attachRight_eq hu0]
  exact (h.attachRightMid hu hx).pull hu

/-- `attachRight` on `[nb, u, x, heap]`. -/
def attachRightBody (pullProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 4 (recAddr 1) ;;
     .store (.bin .add (.reg 4) (.const 1)) (.reg 2) ;;
     .cond (.reg 2) (.store (.bin .add (recAddr 2) (.const 2)) (.reg 1)) .nop ;;
     .cond (.reg 2) (.store (.bin .add (recAddr 2) (.const 3)) (.const 0)) .nop ;;
     .call 5 pullProc [.reg 0, .reg 1, .reg 3] ;;
     .ret (.const 0))

theorem attachRightBody_noRand (pullProc : ℕ) :
    (attachRightBody pullProc).NoRand := by
  simp [attachRightBody, recAddr, Stmt.NoRand]

/-- The summary that `attachRight P st u x` computes is representable. -/
def AttachRightOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : SplayState α σ τ)
    (u x : ℕ) : Prop :=
  u ≠ 0 → ok.sumOk (pullSum P (attachRightMid st u x) u)

/-- The run of `attachRightBody`. -/
theorem attachRightBody_runs {w nb cap u x heap pos pullProc : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (hpull : p.procs[pullProc]? = some (pullBody S.pull))
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hu : u ≤ cap) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap S.space mem) (hok : AttachRightOk ok P st u x) :
    ∃ o st' c, Runs w p ω (attachRightBody pullProc) (startState [nb, u, x, heap] mem pos)
        o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.attachRight P st u x) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧ 0 + c ≤ S.cost + 250 := by
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS := hheap.stride_lt
  have hS6 := Lay.stride_pos
  have hrec := hheap.rec_le
  have hlt : ∀ y ≤ cap, nb + Lay.nodeStride * y + Lay.nodeStride ≤ heap := fun y hy => by
    have := hheap.addr_lt hy; unfold nodeAddr at this; exact this
  have hAu := hlt u hu
  have hAx := hlt x hx
  have hxw : x < 2 ^ w := by
    have : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
    omega
  unfold attachRightBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [SplayState.attachRight] using hnodes, TreeFrame.refl hheap.zero⟩
    · wram_cost
  have hu0 : u ≠ 0 := hcond
  wram_step; try dsimp only
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₁ hM₁ => ?_
  have h₁ : Lay.NodesAt M₁ nb cap (st.setRight u x) ∧ TreeFrame Lay nb cap heap mem M₁ := by
    rw [hM₁]; exact NodesAt.ctrl hnodes (TreeFrame.refl hheap.zero) hu (by decide) hAu
      (fun h => h.setRight Lay hu)
  refine runs_seq_condStore_named_le (by eval_expr) (fun _ => by eval_expr)
    (fun _ => by eval_expr) fun M₂ hM₂ => ?_
  have h₂ : Lay.NodesAt M₂ nb cap (if x = 0 then st.setRight u x else (st.setRight u x).setPar x u)
      ∧ TreeFrame Lay nb cap heap mem M₂ := by
    rw [hM₂]; exact NodesAt.condCtrl h₁.1 h₁.2 hx (by decide) hAx (fun h => h.setPar Lay hx)
  refine runs_seq_condStore_named_le (by eval_expr) (fun _ => by eval_expr)
    (fun _ => by eval_expr) fun M₃ hM₃ => ?_
  have h₃ : Lay.NodesAt M₃ nb cap (attachRightMid st u x) ∧ TreeFrame Lay nb cap heap mem M₃ := by
    have e : attachRightMid st u x = if x = 0 then
        (if x = 0 then st.setRight u x else (st.setRight u x).setPar x u) else
        ((if x = 0 then st.setRight u x else (st.setRight u x).setPar x u).setPpar x 0) := by
      by_cases hx0 : x = 0 <;> simp [attachRightMid, hx0]
    rw [hM₃, e]; exact NodesAt.condCtrl h₂.1 h₂.2 hx (by decide) hAx (fun h => h.setPpar Lay hx)
  refine runs_seq_callBody_le hpull (by eval_expr)
    (R := fun _ st₄ c₄ => Lay.NodesAt st₄.mem nb cap (SplayState.attachRight P st u x) ∧
      TreeFrame Lay nb cap heap mem st₄.mem ∧ c₄ ≤ S.cost + 150) ?_ ?_
  · obtain ⟨o, st', c, hrun, ⟨hn, hf⟩, hc⟩ := pullBody_runs S ω h₃.1
      (hptr.attachRightMid hu hx) hu ⟨hrec, hroom, h₃.2.1, hwide⟩ (fun _ => hok hu0)
    refine ⟨o, st', c, hrun, ?_, h₃.2.trans hf, by omega⟩
    rw [attachRight_eq hu0]; exact hn
  rintro - st₄ c₄ ⟨hN₄, hF₄, hc₄⟩
  wram_step
  · exact ⟨hN₄, hF₄⟩
  · wram_cost

/-! ### `detachRootChildren` -/

/-- Clear the parent and path-parent pointers of `a`, unless `a = 0`. -/
def clearUp (st : SplayState α σ τ) (a : ℕ) : SplayState α σ τ :=
  if a = 0 then st else (st.setPar a 0).setPpar a 0

/-- The pointer writes of `SplayState.detachRootChildren` when `x ≠ 0`. -/
def detachChildrenMid (st : SplayState α σ τ) (x : ℕ) : SplayState α σ τ :=
  ((clearUp (clearUp st (st.nodes x).left) (st.nodes x).right).setLeft x 0).setRight x 0

theorem detachRootChildren_eq {P : LctPayload α σ τ} {st : SplayState α σ τ} {x : ℕ}
    (hx : x ≠ 0) :
    SplayState.detachRootChildren P st x = SplayState.pull P (detachChildrenMid st x) x := by
  simp only [SplayState.detachRootChildren, detachChildrenMid, clearUp, hx, if_false]

theorem PtrOk.clearUp {cap a : ℕ} {st : SplayState α σ τ} (h : PtrOk cap st) (ha : a ≤ cap) :
    PtrOk cap (Gen.clearUp st a) := by
  unfold Gen.clearUp
  split_ifs
  · exact h
  · exact (h.setPar ha (Nat.zero_le _)).setPpar ha (Nat.zero_le _)

theorem PtrOk.detachChildrenMid {cap x : ℕ} {st : SplayState α σ τ} (h : PtrOk cap st)
    (hx : x ≤ cap) : PtrOk cap (Gen.detachChildrenMid st x) := by
  obtain ⟨hl, hr, -, -⟩ := h x hx
  unfold Gen.detachChildrenMid
  exact (((h.clearUp hl).clearUp hr).setLeft hx (Nat.zero_le _)).setRight hx (Nat.zero_le _)

theorem PtrOk.detachRootChildren {cap x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.detachRootChildren P st x) := by
  by_cases hx0 : x = 0
  · simpa [SplayState.detachRootChildren, hx0] using h
  rw [detachRootChildren_eq hx0]
  exact (h.detachChildrenMid hx).pull hx

/-- `detachRootChildren` on `[nb, x, heap]`. It notes `x` and both former children. -/
def detachRootChildrenBody (pullProc noteProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 3 (recAddr 1) ;;
     .assign 4 (.load (.reg 3)) ;;
     .assign 5 (.load (.bin .add (.reg 3) (.const 1))) ;;
     .cond (.reg 4) (.store (.bin .add (recAddr 4) (.const 2)) (.const 0)) .nop ;;
     .cond (.reg 4) (.store (.bin .add (recAddr 4) (.const 3)) (.const 0)) .nop ;;
     .cond (.reg 5) (.store (.bin .add (recAddr 5) (.const 2)) (.const 0)) .nop ;;
     .cond (.reg 5) (.store (.bin .add (recAddr 5) (.const 3)) (.const 0)) .nop ;;
     .store (.reg 3) (.const 0) ;;
     .store (.bin .add (.reg 3) (.const 1)) (.const 0) ;;
     .call 6 pullProc [.reg 0, .reg 1, .reg 2] ;;
     .call 6 noteProc [.reg 0, .reg 1] ;;
     .call 6 noteProc [.reg 0, .reg 4] ;;
     .call 6 noteProc [.reg 0, .reg 5] ;;
     .ret (.const 0))

theorem detachRootChildrenBody_noRand (pullProc noteProc : ℕ) :
    (detachRootChildrenBody pullProc noteProc).NoRand := by
  simp [detachRootChildrenBody, recAddr, Stmt.NoRand]

/-- The summary that `detachRootChildren P st x` computes is representable. -/
def DetachChildrenOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : SplayState α σ τ)
    (x : ℕ) : Prop :=
  x ≠ 0 → ok.sumOk (pullSum P (detachChildrenMid st x) x)

/-- The nodes `detachRootChildren` notes: `x`, then both former children. -/
def dcNotes (st : SplayState α σ τ) (x : ℕ) (S : List ℕ) : List ℕ :=
  if x = 0 then S
  else noteList (noteList (noteList S x) (st.nodes x).left) (st.nodes x).right

theorem clearUp_split (st : SplayState α σ τ) (a : ℕ) :
    clearUp st a = if a = 0 then (if a = 0 then st else st.setPar a 0) else
      (if a = 0 then st else st.setPar a 0).setPpar a 0 := by
  by_cases ha : a = 0 <;> simp [clearUp, ha]

/-- The run of `detachRootChildrenBody`. -/
theorem detachRootChildrenBody_runs {w nb cap x heap pos pullProc noteProc : ℕ}
    {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (hpull : p.procs[pullProc]? = some (pullBody S.pull))
    (hnote : p.procs[noteProc]? = some noteBody)
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ} {I : List ℕ}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap S.space mem) (hok : DetachChildrenOk ok P st x)
    (hnb : 2 * cap + 3 ≤ nb) (hI : IdxAt mem nb cap I) :
    ∃ o st' c, Runs w p ω (detachRootChildrenBody pullProc noteProc)
        (startState [nb, x, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.detachRootChildren P st x) ∧
        IdxFrame Lay nb cap heap mem st'.mem (dcNotes st x I)) ∧ 0 + c ≤ S.cost + 600 := by
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS := hheap.stride_lt
  have hS6 := Lay.stride_pos
  have hrec := hheap.rec_le
  have hlt : ∀ y ≤ cap, nb + Lay.nodeStride * y + Lay.nodeStride ≤ heap := fun y hy => by
    have := hheap.addr_lt hy; unfold nodeAddr at this; exact this
  obtain ⟨hlc, hrc, -, -⟩ := hptr x hx
  set a := (st.nodes x).left with ha
  set b := (st.nodes x).right with hb
  have hm0 : mem (nb + Lay.nodeStride * x) = a := (hnodes x hx).1
  have hm1 : mem (nb + Lay.nodeStride * x + 1) = b := (hnodes x hx).2.1
  have hAx := hlt x hx
  have hAa := hlt a hlc
  have hAb := hlt b hrc
  have haS : a ≤ Lay.nodeStride * a := Nat.le_mul_of_pos_left a (by omega)
  have hbS : b ≤ Lay.nodeStride * b := Nat.le_mul_of_pos_left b (by omega)
  have haw : Lay.nodeStride * (st.nodes x).left < 2 ^ w := by rw [← ha]; omega
  have hbw : Lay.nodeStride * (st.nodes x).right < 2 ^ w := by rw [← hb]; omega
  have haw' : nb + Lay.nodeStride * (st.nodes x).left + 3 < 2 ^ w := by rw [← ha]; omega
  have hbw' : nb + Lay.nodeStride * (st.nodes x).right + 3 < 2 ^ w := by rw [← hb]; omega
  unfold detachRootChildrenBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  have hnh : nb ≤ heap := by have := hlt 0 (Nat.zero_le _); omega
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [SplayState.detachRootChildren] using hnodes,
        IdxFrame.refl hheap.zero (by simpa [dcNotes] using hI)⟩
    · wram_cost
  have hx0 : x ≠ 0 := hcond
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hm0]
  wram_step; try dsimp only
  rw [hm1]
  refine runs_seq_condStore_named_le (by eval_expr) (fun _ => by eval_expr)
    (fun _ => by eval_expr) fun M₁ hM₁ => ?_
  have h₁ : Lay.NodesAt M₁ nb cap (if a = 0 then st else st.setPar a 0) ∧
      TreeFrame Lay nb cap heap mem M₁ := by
    rw [hM₁]; exact NodesAt.condCtrl hnodes (TreeFrame.refl hheap.zero) hlc (by decide) hAa
      (fun h => h.setPar Lay hlc)
  refine runs_seq_condStore_named_le (by eval_expr) (fun _ => by eval_expr)
    (fun _ => by eval_expr) fun M₂ hM₂ => ?_
  have h₂ : Lay.NodesAt M₂ nb cap (clearUp st a) ∧ TreeFrame Lay nb cap heap mem M₂ := by
    rw [hM₂, clearUp_split]
    exact NodesAt.condCtrl h₁.1 h₁.2 hlc (by decide) hAa (fun h => h.setPpar Lay hlc)
  refine runs_seq_condStore_named_le (by eval_expr) (fun _ => by eval_expr)
    (fun _ => by eval_expr) fun M₃ hM₃ => ?_
  have h₃ : Lay.NodesAt M₃ nb cap (if b = 0 then clearUp st a else (clearUp st a).setPar b 0) ∧
      TreeFrame Lay nb cap heap mem M₃ := by
    rw [hM₃]; exact NodesAt.condCtrl h₂.1 h₂.2 hrc (by decide) hAb (fun h => h.setPar Lay hrc)
  refine runs_seq_condStore_named_le (by eval_expr) (fun _ => by eval_expr)
    (fun _ => by eval_expr) fun M₄ hM₄ => ?_
  have h₄ : Lay.NodesAt M₄ nb cap (clearUp (clearUp st a) b) ∧
      TreeFrame Lay nb cap heap mem M₄ := by
    rw [hM₄, clearUp_split (clearUp st a) b]
    exact NodesAt.condCtrl h₃.1 h₃.2 hrc (by decide) hAb (fun h => h.setPpar Lay hrc)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₅ hM₅ => ?_
  have h₅ : Lay.NodesAt M₅ nb cap ((clearUp (clearUp st a) b).setLeft x 0) ∧
      TreeFrame Lay nb cap heap mem M₅ := by
    rw [hM₅]; exact NodesAt.ctrl h₄.1 h₄.2 hx (by decide) hAx (fun h => h.setLeft Lay hx)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₆ hM₆ => ?_
  have h₆ : Lay.NodesAt M₆ nb cap (detachChildrenMid st x) ∧ TreeFrame Lay nb cap heap mem M₆ := by
    rw [hM₆]; exact NodesAt.ctrl h₅.1 h₅.2 hx (by decide) hAx (fun h => h.setRight Lay hx)
  refine runs_seq_callBody_le hpull (by eval_expr)
    (R := fun _ st₇ c₇ => Lay.NodesAt st₇.mem nb cap (SplayState.detachRootChildren P st x) ∧
      TreeFrame Lay nb cap heap mem st₇.mem ∧ c₇ ≤ S.cost + 150) ?_ ?_
  · obtain ⟨o, st', c, hrun, ⟨hn, hf⟩, hc⟩ := pullBody_runs S ω h₆.1
      (hptr.detachChildrenMid hx) hx ⟨hrec, hroom, h₆.2.1, hwide⟩ (fun _ => hok hx0)
    refine ⟨o, st', c, hrun, ?_, h₆.2.trans hf, by omega⟩
    rw [detachRootChildren_eq hx0]; exact hn
  rintro - st₇ c₇ ⟨hN₇, hF₇, hc₇⟩
  have hF₇' := (IdxFrame.refl hheap.zero hI).trans_tree hnb hnh hF₇
  refine runs_seq_note (S := I) hnote (by eval_expr) (by eval_expr) hx hnb hnh
    (by omega) hN₇ hF₇' rfl fun v₈ m₈ hN₈ hF₈ => ?_
  refine runs_seq_note (S := noteList I x) hnote (by eval_expr) (by eval_expr) hlc hnb hnh
    (by omega) hN₈ hF₈ rfl fun v₉ m₉ hN₉ hF₉ => ?_
  refine runs_seq_note (S := noteList (noteList I x) a) hnote (by eval_expr) (by eval_expr) hrc
    hnb hnh (by omega) hN₉ hF₉ rfl fun v₁₀ m₁₀ hN₁₀ hF₁₀ => ?_
  wram_step
  · exact ⟨hN₁₀, by simpa [dcNotes, hx0, ← ha, ← hb] using hF₁₀⟩
  · wram_cost

end MinCostFlow.LinkCut.Gen
