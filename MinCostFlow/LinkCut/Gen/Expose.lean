module

public import MinCostFlow.LinkCut.Gen.Walk

/-!
# `expose` as a program

`exposeLoopBody` is the machine version of `lctExposeLoop`: while the current node has a path
parent `p`, it splays `p`, cuts off the right child of `p`, and hangs the current tree there.
`exposeBody` is the machine version of `lctExposeCost` (splay, detach, loop, splay).

The splay fuel `2 n + 1` is passed as an argument. The loop is recursive, with its own fuel as
another argument, like the model. Only the `splay` part of the state lives in the records; the
model's `n` and `freeHead` do not change here.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-- `lctExposeLoop` on `[nb, last, fuel, splayFuel, heap]`. -/
def exposeLoopBody (splayProc drProc arProc selfProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 0))
    (.assign 5 (.load (.bin .add (recAddr 1) (.const 3))) ;;
     .cond (.bin .eq (.reg 5) (.const 0)) (.ret (.const 0))
       (.call 6 splayProc [.reg 0, .reg 5, .reg 3, .reg 4] ;;
        .call 6 drProc [.reg 0, .reg 5, .reg 4] ;;
        .call 6 arProc [.reg 0, .reg 5, .reg 1, .reg 4] ;;
        .call 6 selfProc [.reg 0, .reg 5, .bin .sub (.reg 2) (.const 1), .reg 3, .reg 4] ;;
        .ret (.const 0)))

theorem exposeLoopBody_noRand (a b c d : ℕ) :
    (exposeLoopBody a b c d).NoRand := by
  simp [exposeLoopBody, recAddr, Stmt.NoRand]

/-- `lctExposeCost` on `[nb, v, splayFuel, heap]`. -/
def exposeBody (splayProc drProc loopProc : ℕ) : Stmt :=
  .call 4 splayProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .call 4 drProc [.reg 0, .reg 1, .reg 3] ;;
  .call 4 loopProc [.reg 0, .reg 1, .reg 2, .reg 2, .reg 3] ;;
  .call 4 splayProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .ret (.const 0)

theorem exposeBody_noRand (a b c : ℕ) : (exposeBody a b c).NoRand := by
  simp [exposeBody, Stmt.NoRand]

/-- The procedures `expose` needs, at their indices in the program. -/
structure ExposeProcs {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} {S : PayloadSteps w p P Lay ok} {L : LazyProcs w p P Lay ok S}
    (Q : SplayProcs L) where
  detachRight : ℕ
  attachRight : ℕ
  loop : ℕ
  expose : ℕ
  note : ℕ
  note_body : p.procs[note]? = some noteBody
  detachRight_body : p.procs[detachRight]? = some (detachRightBody Q.pull note)
  attachRight_body : p.procs[attachRight]? = some (attachRightBody Q.pull)
  loop_body : p.procs[loop]? = some (exposeLoopBody Q.splay detachRight attachRight loop)
  expose_body : p.procs[expose]? = some (exposeBody Q.splay detachRight loop)

theorem lctExposeStep_splay (P : LctPayload α σ τ) (st : LctState α σ τ) (last : ℕ) :
    (lctExposeStep P st last).1.splay =
      SplayState.attachRight P (SplayState.detachRight P (SplayState.splay P st.splay
        (2 * st.n + 1) (st.splay.nodes last).ppar) (st.splay.nodes last).ppar)
        (st.splay.nodes last).ppar last := rfl

theorem PtrOk.exposeStep {cap last : ℕ} {P : LctPayload α σ τ} {st : LctState α σ τ}
    (h : PtrOk cap st.splay) (hl : last ≤ cap) : PtrOk cap (lctExposeStep P st last).1.splay := by
  have hp := (h last hl).2.2.2
  rw [lctExposeStep_splay]
  exact ((h.splay hp).detachRight hp).attachRight hp hl

/-- The payload values of the loop `lctExposeLoop P st fuel last` are representable. -/
def ExposeLoopOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) : LctState α σ τ → ℕ → ℕ → Prop
  | _, 0, _ => True
  | st, k + 1, last => (st.splay.nodes last).ppar ≠ 0 →
      SplayOk ok P st.splay (2 * st.n + 1) (st.splay.nodes last).ppar ∧
      DetachRightOk ok P (SplayState.splay P st.splay (2 * st.n + 1) (st.splay.nodes last).ppar)
        (st.splay.nodes last).ppar ∧
      AttachRightOk ok P (SplayState.detachRight P (SplayState.splay P st.splay (2 * st.n + 1)
        (st.splay.nodes last).ppar) (st.splay.nodes last).ppar) (st.splay.nodes last).ppar last ∧
      ExposeLoopOk ok P (lctExposeStep P st last).1 k (st.splay.nodes last).ppar

/-- The cost bound of `lctExposeLoop P st fuel last`. -/
def exposeLoopCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) : LctState α σ τ → ℕ → ℕ → ℕ
  | _, 0, _ => 0
  | st, k + 1, last =>
      if (st.splay.nodes last).ppar = 0 then 0
      else splayCost S st.splay (2 * st.n + 1) (st.splay.nodes last).ppar + 2 * S.cost + 900 +
        exposeLoopCost S (lctExposeStep P st last).1 k (st.splay.nodes last).ppar

theorem PtrOk.exposeLoop {cap : ℕ} {P : LctPayload α σ τ} :
    ∀ (k last : ℕ) {st : LctState α σ τ}, PtrOk cap st.splay → last ≤ cap →
      PtrOk cap (lctExposeLoop P st k last).1.splay
  | 0, _, _, h, _ => h
  | k + 1, last, st, h, hl => by
    unfold lctExposeLoop
    split_ifs
    · exact h
    · exact PtrOk.exposeLoop k _ (h.exposeStep hl) (h last hl).2.2.2

/-- The nodes the loop `lctExposeLoop P st fuel last` notes: those of each `detachRight`. -/
def exposeLoopNotes (P : LctPayload α σ τ) : LctState α σ τ → ℕ → ℕ → List ℕ → List ℕ
  | _, 0, _, S => S
  | st, k + 1, last, S =>
      if (st.splay.nodes last).ppar = 0 then S
      else exposeLoopNotes P (lctExposeStep P st last).1 k (st.splay.nodes last).ppar
        (drNotes (SplayState.splay P st.splay (2 * st.n + 1) (st.splay.nodes last).ppar)
          (st.splay.nodes last).ppar S)

/-- The run of `exposeLoopBody`. -/
theorem exposeLoopBody_runs {w nb cap heap : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    {S : PayloadSteps w p P Lay ok} {L : LazyProcs w p P Lay ok S} {Q : SplayProcs L}
    (E : ExposeProcs Q) (ω : ℕ → Bool) :
    ∀ (k last pos : ℕ) {mem : ℕ → ℕ} {st : LctState α σ τ},
    Lay.NodesAt mem nb cap st.splay → PtrOk cap st.splay → last ≤ cap →
    HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem → k < 2 ^ w →
    2 * st.n + 1 < 2 ^ w → ExposeLoopOk ok P st k last →
    2 * cap + 3 ≤ nb → ∀ {I : List ℕ}, IdxAt mem nb cap I →
    ∃ o st' c, Runs w p ω (exposeLoopBody Q.splay E.detachRight E.attachRight E.loop)
        (startState [nb, last, k, 2 * st.n + 1, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (lctExposeLoop P st k last).1.splay ∧
        IdxFrame Lay nb cap heap mem st'.mem (exposeLoopNotes P st k last I)) ∧
      0 + c ≤ exposeLoopCost S st k last + 50
  | 0, last, pos, mem, st, hnodes, hptr, hl, hheap, hk, hn, hok, hnb, I, hI => by
    have hwide := hheap.wide
    unfold exposeLoopBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step
    · wram_step
      · exact ⟨by simpa [lctExposeLoop] using hnodes, IdxFrame.refl hheap.zero hI⟩
      · simp only [exposeLoopCost]; wram_cost
  | k + 1, last, pos, mem, st, hnodes, hptr, hl, hheap, hk, hn, hok, hnb, I, hI => by
    have hnh := hheap.nb_le
    have hroom := hheap.room
    have hwide := hheap.wide
    have hS := hheap.stride_lt
    have hS6 := Lay.stride_pos
    have hA := hheap.addr_lt hl
    have hlS : last ≤ Lay.nodeStride * last := Nat.le_mul_of_pos_left last (by omega)
    unfold nodeAddr at hA
    have hpc := (hptr last hl).2.2.2
    set pp := (st.splay.nodes last).ppar with hpp
    have hm3 : mem (nb + Lay.nodeStride * last + 3) = pp := (hnodes last hl).2.2.2.1
    have hpS : pp ≤ Lay.nodeStride * pp := Nat.le_mul_of_pos_left pp (by omega)
    have hAp := hheap.addr_lt hpc
    unfold nodeAddr at hAp
    unfold exposeLoopBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step
    wram_step; try dsimp only
    rw [hm3]
    wram_step
    · have hp0 : pp = 0 := hcond
      wram_step
      · exact ⟨by simpa [lctExposeLoop, ← hpp, hp0] using hnodes,
          IdxFrame.refl hheap.zero (by simpa [exposeLoopNotes, ← hpp, hp0] using hI)⟩
      · simp only [exposeLoopCost, ← hpp, hp0, if_true]; wram_cost
    have hp0 : pp ≠ 0 := hcond
    obtain ⟨ok₁, ok₂, ok₃, ok₄⟩ := hok hp0
    set s₁ := SplayState.splay P st.splay (2 * st.n + 1) pp with hs₁
    set s₂ := SplayState.detachRight P s₁ pp with hs₂
    have hP₁ : PtrOk cap s₁ := hptr.splay hpc
    have hP₂ : PtrOk cap s₂ := hP₁.detachRight hpc
    have hcost : exposeLoopCost S st (k + 1) last = splayCost S st.splay (2 * st.n + 1) pp +
        2 * S.cost + 900 + exposeLoopCost S (lctExposeStep P st last).1 k pp := by
      simp [exposeLoopCost, ← hpp, hp0]
    have hnotes : exposeLoopNotes P st (k + 1) last I =
        exposeLoopNotes P (lctExposeStep P st last).1 k pp (drNotes s₁ pp I) := by
      simp [exposeLoopNotes, ← hpp, hp0, hs₁]
    have hloop : (lctExposeLoop P st (k + 1) last).1 =
        (lctExposeLoop P (lctExposeStep P st last).1 k pp).1 := by
      simp [lctExposeLoop, ← hpp, hp0, lctExposeStep]
    refine runs_seq_callBody_le Q.splay_body (by eval_expr)
      (R := fun _ m₁ c₁ => Lay.NodesAt m₁.mem nb cap s₁ ∧
        TreeFrame Lay nb cap heap mem m₁.mem ∧
        c₁ ≤ splayCost S st.splay (2 * st.n + 1) pp) ?_ ?_
    · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := splayBody_runs Q ω (pos := pos) hnodes hptr hpc
        hheap hn ok₁
      exact ⟨o, st', c, by simpa using hr, hn', hf, by omega⟩
    rintro - m₁ c₁ ⟨hn₁, hf₁, hc₁⟩
    refine runs_seq_callBody_le E.detachRight_body (by eval_expr)
      (R := fun _ m₂ c₂ => Lay.NodesAt m₂.mem nb cap s₂ ∧
        IdxFrame Lay nb cap heap mem m₂.mem (drNotes s₁ pp I) ∧ c₂ ≤ S.cost + 400) ?_ ?_
    · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := detachRightBody_runs S Q.pull_body E.note_body ω
        (pos := m₁.pos) hn₁ hP₁ hpc ⟨hheap.rec_le, by omega, hf₁.1, hwide⟩ ok₂ hnb
        (hI.of_treeFrame hnb hnh hf₁)
      exact ⟨o, st', c, by simpa using hr, hn', (IdxFrame.of_treeFrame hI hnb hnh hf₁).trans hf, by omega⟩
    rintro - m₂ c₂ ⟨hn₂, hf₂, hc₂⟩
    refine runs_seq_callBody_le E.attachRight_body (by eval_expr)
      (R := fun _ m₃ c₃ => Lay.NodesAt m₃.mem nb cap (lctExposeStep P st last).1.splay ∧
        IdxFrame Lay nb cap heap mem m₃.mem (drNotes s₁ pp I) ∧ c₃ ≤ S.cost + 250) ?_ ?_
    · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := attachRightBody_runs S Q.pull_body ω
        (pos := m₂.pos) hn₂ hP₂ hpc hl ⟨hheap.rec_le, by omega, hf₂.1.1, hwide⟩ ok₃
      exact ⟨o, st', c, by simpa using hr, hn', hf₂.trans_tree hnb hnh hf, by omega⟩
    rintro - m₃ c₃ ⟨hn₃, hf₃, hc₃⟩
    refine runs_seq_callBody_le E.loop_body (by eval_expr)
      (R := fun _ m₄ c₄ => Lay.NodesAt m₄.mem nb cap (lctExposeLoop P st (k + 1) last).1.splay ∧
        IdxFrame Lay nb cap heap mem m₄.mem (exposeLoopNotes P st (k + 1) last I) ∧
        c₄ ≤ exposeLoopCost S (lctExposeStep P st last).1 k pp + 50) ?_ ?_
    · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := exposeLoopBody_runs E ω k pp m₃.pos hn₃
        (hptr.exposeStep hl) hpc ⟨hheap.rec_le, hroom, hf₃.1.1, hwide⟩ (by omega) hn ok₄ hnb
        hf₃.2
      refine ⟨o, st', c, by simpa [lctExposeStep] using hr, ?_, ?_, by omega⟩
      · rw [hloop]; exact hn'
      · rw [hnotes]; exact hf₃.trans hf
    rintro - m₄ c₄ ⟨hn₄, hf₄, hc₄⟩
    wram_step
    · exact ⟨hn₄, hf₄⟩
    · rw [hcost]
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
        argsSize_cons, argsSize_nil] at *
      omega

/-- The state after the first splay and detach of `lctExposeCost P st v`. -/
def exposeStart (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) : LctState α σ τ :=
  { n := st.n, splay := SplayState.detachRight P (SplayState.splay P st.splay (2 * st.n + 1) v) v,
    freeHead := st.freeHead }

theorem lctExpose_splay (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    (lctExpose P st v).splay = SplayState.splay P
      (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).1.splay (2 * st.n + 1) v := rfl

theorem lctExpose_n (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    (lctExpose P st v).n = st.n := rfl

theorem lctExpose_freeHead (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    (lctExpose P st v).freeHead = st.freeHead := by
  show (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).1.freeHead = st.freeHead
  rw [lctExposeLoop_freeHead]; rfl

theorem PtrOk.expose {cap v : ℕ} {P : LctPayload α σ τ} {st : LctState α σ τ}
    (h : PtrOk cap st.splay) (hv : v ≤ cap) : PtrOk cap (lctExpose P st v).splay := by
  rw [lctExpose_splay]
  exact (PtrOk.exposeLoop _ v ((h.splay hv).detachRight hv) hv).splay hv

/-- The payload values of `lctExpose P st v` are representable. -/
def ExposeOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    Prop :=
  SplayOk ok P st.splay (2 * st.n + 1) v ∧
  DetachRightOk ok P (SplayState.splay P st.splay (2 * st.n + 1) v) v ∧
  ExposeLoopOk ok P (exposeStart P st v) (2 * st.n + 1) v ∧
  SplayOk ok P (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).1.splay (2 * st.n + 1) v

/-- The cost bound of `lctExpose P st v`. -/
def exposeCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) (st : LctState α σ τ) (v : ℕ) : ℕ :=
  splayCost S st.splay (2 * st.n + 1) v + S.cost +
    exposeLoopCost S (exposeStart P st v) (2 * st.n + 1) v +
    splayCost S (lctExposeLoop P (exposeStart P st v) (2 * st.n + 1) v).1.splay
      (2 * st.n + 1) v + 600

/-- The nodes `lctExpose P st v` notes. -/
def exposeNotes (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) (S : List ℕ) : List ℕ :=
  exposeLoopNotes P (exposeStart P st v) (2 * st.n + 1) v
    (drNotes (SplayState.splay P st.splay (2 * st.n + 1) v) v S)

/-- The run of `exposeBody`. -/
theorem exposeBody_runs {w nb cap heap v pos : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    {S : PayloadSteps w p P Lay ok} {L : LazyProcs w p P Lay ok S} {Q : SplayProcs L}
    (E : ExposeProcs Q) (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : LctState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st.splay) (hptr : PtrOk cap st.splay) (hv : v ≤ cap)
    (hheap : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem)
    (hn : 2 * st.n + 1 < 2 ^ w) (hok : ExposeOk ok P st v)
    (hnb : 2 * cap + 3 ≤ nb) {I : List ℕ} (hI : IdxAt mem nb cap I) :
    ∃ o st' c, Runs w p ω (exposeBody Q.splay E.detachRight E.loop)
        (startState [nb, v, 2 * st.n + 1, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (lctExpose P st v).splay ∧
        IdxFrame Lay nb cap heap mem st'.mem (exposeNotes P st v I)) ∧
      0 + c ≤ exposeCost S st v := by
  have hnh := hheap.nb_le
  have hroom := hheap.room
  have hwide := hheap.wide
  obtain ⟨ok₁, ok₂, ok₃, ok₄⟩ := hok
  set F := 2 * st.n + 1 with hF
  set s₁ := SplayState.splay P st.splay F v with hs₁
  set st₂ := exposeStart P st v with hst₂
  set st₃ := (lctExposeLoop P st₂ F v).1 with hst₃
  have hP₁ : PtrOk cap s₁ := hptr.splay hv
  have hP₂ : PtrOk cap st₂.splay := hP₁.detachRight hv
  have hP₃ : PtrOk cap st₃.splay := PtrOk.exposeLoop _ v hP₂ hv
  unfold exposeBody
  rw [startState]
  refine runs_seq_callBody_le Q.splay_body (by eval_expr)
    (R := fun _ m₁ c₁ => Lay.NodesAt m₁.mem nb cap s₁ ∧
      TreeFrame Lay nb cap heap mem m₁.mem ∧ c₁ ≤ splayCost S st.splay F v) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := splayBody_runs Q ω (pos := pos) hnodes hptr hv
      hheap hn ok₁
    exact ⟨o, st', c, by simpa using hr, hn', hf, by omega⟩
  rintro - m₁ c₁ ⟨hn₁, hf₁, hc₁⟩
  refine runs_seq_callBody_le E.detachRight_body (by eval_expr)
    (R := fun _ m₂ c₂ => Lay.NodesAt m₂.mem nb cap st₂.splay ∧
      IdxFrame Lay nb cap heap mem m₂.mem (drNotes s₁ v I) ∧ c₂ ≤ S.cost + 400) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := detachRightBody_runs S Q.pull_body E.note_body ω
      (pos := m₁.pos) hn₁ hP₁ hv ⟨hheap.rec_le, by omega, hf₁.1, hwide⟩ ok₂ hnb
      (hI.of_treeFrame hnb hnh hf₁)
    exact ⟨o, st', c, by simpa using hr, hn', (IdxFrame.of_treeFrame hI hnb hnh hf₁).trans hf, by omega⟩
  rintro - m₂ c₂ ⟨hn₂, hf₂, hc₂⟩
  refine runs_seq_callBody_le E.loop_body (by eval_expr)
    (R := fun _ m₃ c₃ => Lay.NodesAt m₃.mem nb cap st₃.splay ∧
      IdxFrame Lay nb cap heap mem m₃.mem (exposeNotes P st v I) ∧
      c₃ ≤ exposeLoopCost S st₂ F v + 50) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := exposeLoopBody_runs E ω F v m₂.pos hn₂ hP₂ hv
      ⟨hheap.rec_le, hroom, hf₂.1.1, hwide⟩ hn hn ok₃ hnb hf₂.2
    exact ⟨o, st', c, by simpa [st₂, exposeStart] using hr, hn', hf₂.trans hf, by omega⟩
  rintro - m₃ c₃ ⟨hn₃, hf₃, hc₃⟩
  refine runs_seq_callBody_le Q.splay_body (by eval_expr)
    (R := fun _ m₄ c₄ => Lay.NodesAt m₄.mem nb cap (lctExpose P st v).splay ∧
      IdxFrame Lay nb cap heap mem m₄.mem (exposeNotes P st v I) ∧
      c₄ ≤ splayCost S st₃.splay F v) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := splayBody_runs Q ω (pos := m₃.pos) hn₃ hP₃ hv
      ⟨hheap.rec_le, hroom, hf₃.1.1, hwide⟩ hn ok₄
    exact ⟨o, st', c, by simpa using hr, hn', hf₃.trans_tree hnb hnh hf, by omega⟩
  rintro - m₄ c₄ ⟨hn₄, hf₄, hc₄⟩
  wram_step
  · exact ⟨hn₄, hf₄⟩
  · simp only [exposeCost, ← hF, ← hst₂, ← hst₃]
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil] at *
    omega

end MinCostFlow.LinkCut.Gen
