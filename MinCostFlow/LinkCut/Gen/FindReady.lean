module

public import MinCostFlow.LinkCut.Gen.Descend
public import MinCostFlow.LinkCut.Gen.Expose

/-!
# Find-ready as a program

The ready index is a stack of node ids (`Gen/Index.lean`). Find-ready looks at the top entry `x`
and tests it with `ValidG`, which reads only the record of `x`: `x` is a node, it has parent
`0`, its summary is ready, and it has a child or a path parent. If the test fails, it pops `x`
and tries again. If it holds, it walks down from `x` to a node `y` with a ready value
(`descendBody`), exposes `y`, and returns `y`; `x` stays on the stack. If the stack is empty, it
returns `0`.

`findLoop` is the model, on the stack listed from the top down. `findReadyBody_runs` shows that
the program follows it. Its cost is at most `findCost`: a constant for each popped entry, and
the cost of the descent and of the expose at the end.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout MinCostFlow.LinkCut.PathTree

variable {α σ τ : Type*}

/-- The test on the top entry: a node with parent `0`, a ready summary, and a child or a path
parent. -/
def ValidG (rs : σ → Bool) (n : ℕ) (s : SplayState α σ τ) (x : ℕ) : Prop :=
  1 ≤ x ∧ x < 2 * n ∧ (s.nodes x).par = 0 ∧ rs (s.nodes x).sum = true ∧
    ((s.nodes x).left ≠ 0 ∨ (s.nodes x).right ≠ 0 ∨ (s.nodes x).ppar ≠ 0)

instance (rs : σ → Bool) (n : ℕ) (s : SplayState α σ τ) (x : ℕ) :
    Decidable (ValidG rs n s x) := by
  unfold ValidG; infer_instance

/-- The state after the descent from `x`. -/
def descState (P : LctPayload α σ τ) (rs : σ → Bool) (rv : α → Bool) (st : LctState α σ τ)
    (x : ℕ) : LctState α σ τ :=
  { st with splay := (descend P rs rv st.splay (2 * st.n + 1) x).1 }

/-- The node the descent from `x` stops at. -/
def descNode (P : LctPayload α σ τ) (rs : σ → Bool) (rv : α → Bool) (st : LctState α σ τ)
    (x : ℕ) : ℕ :=
  (descend P rs rv st.splay (2 * st.n + 1) x).2

/-- Find-ready in the model, on the stack listed from the top down: the new state, the new stack
(bottom first), and the answer. -/
def findLoop (P : LctPayload α σ τ) (rs : σ → Bool) (rv : α → Bool) (st : LctState α σ τ) :
    List ℕ → LctState α σ τ × List ℕ × ℕ
  | [] => (st, [], 0)
  | x :: R =>
    if ValidG rs st.n st.splay x then
      (lctExpose P (descState P rs rv st x) (descNode P rs rv st x),
        exposeNotes P (descState P rs rv st x) (descNode P rs rv st x) (x :: R).reverse,
        descNode P rs rv st x)
    else findLoop P rs rv st R

/-- The payload values that find-ready computes are representable. -/
def FindOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (rs : σ → Bool) (rv : α → Bool)
    (st : LctState α σ τ) : List ℕ → Prop
  | [] => True
  | x :: R =>
    if ValidG rs st.n st.splay x then
      DescendOk ok P rs rv st.splay (2 * st.n + 1) x ∧
        ExposeOk ok P (descState P rs rv st x) (descNode P rs rv st x)
    else FindOk ok P rs rv st R

/-- A bound on the cost of find-ready. -/
def findCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} {rs : σ → Bool} {rv : α → Bool} (S : PayloadSteps w p P Lay ok)
    (T : ReadyTests w p Lay rs rv) (st : LctState α σ τ) : List ℕ → ℕ
  | [] => 50
  | x :: R =>
    if ValidG rs st.n st.splay x then
      (descendSteps P rs rv st.splay (2 * st.n + 1) x + 1) * (pushDownCost S + 2 * T.cost + 120) +
        exposeCost S (descState P rs rv st x) (descNode P rs rv st x) + T.cost + 300
    else T.cost + 300 + findCost S T st R

/-- `findReady [nb, F, heap]` with `F = 2 n + 1`. `selfProc` is this procedure. -/
def findReadyBody (selfProc descProc exposeProc sumProc popProc : ℕ) : Stmt :=
  strideLoad ;;
  .assign 3 (.load (.bin .sub (.reg 0) (.const 1))) ;;
  .cond (.bin .eq (.reg 3) (.const 0)) (.ret (.const 0))
    (.assign 4 (.load (.bin .sub (.reg 0) (.bin .add (.bin .add (.reg 3) (.reg 3)) (.const 1)))) ;;
     .assign 5 (recAddr 4) ;;
     .call 6 sumProc [.reg 5] ;;
     .cond (.bin .mul (.bin .mul (.bin .mul (.bin .mul
        (.bin .lt (.const 0) (.reg 4))
        (.bin .lt (.reg 4) (.bin .sub (.reg 1) (.const 1))))
        (.bin .eq (.load (.bin .add (.reg 5) (.const 2))) (.const 0)))
        (.reg 6))
        (.bin .lt (.const 0) (.bin .add (.bin .add
          (.bin .lt (.const 0) (.load (.reg 5)))
          (.bin .lt (.const 0) (.load (.bin .add (.reg 5) (.const 1)))))
          (.bin .lt (.const 0) (.load (.bin .add (.reg 5) (.const 3)))))))
      (.call 7 descProc [.reg 0, .reg 4, .reg 1, .reg 2] ;;
       .call 8 exposeProc [.reg 0, .reg 7, .reg 1, .reg 2] ;;
       .ret (.reg 7))
      (.call 7 popProc [.reg 0] ;;
       .call 8 selfProc [.reg 0, .reg 1, .reg 2] ;;
       .ret (.reg 8)))

theorem findReadyBody_noRand (a b c d e : ℕ) :
    (findReadyBody a b c d e).NoRand := by
  simp [findReadyBody, recAddr, Stmt.NoRand]

/-- The value the program computes for the test, as a number. -/
theorem validG_val_iff (rs : σ → Bool) (n : ℕ) (s : SplayState α σ τ) (x : ℕ) :
    ((if 0 < x then 1 else 0) * (if x < 2 * n + 1 - 1 then 1 else 0) *
      (if (s.nodes x).par = 0 then 1 else 0) * (if rs (s.nodes x).sum then 1 else 0) *
      (if 0 < (if 0 < (s.nodes x).left then 1 else 0) + (if 0 < (s.nodes x).right then 1 else 0) +
        (if 0 < (s.nodes x).ppar then 1 else 0) then 1 else 0) ≠ 0) ↔
      ValidG rs n s x := by
  unfold ValidG
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · by_contra hc; simp_all
    · by_contra hc; simp_all
    · by_contra hc; simp_all
    · by_contra hc; simp_all
    · by_contra hc; push_neg at hc; simp_all
  · rintro ⟨h1, h2, h3, h4, h5⟩
    have : 0 < (if 0 < (s.nodes x).left then 1 else 0) + (if 0 < (s.nodes x).right then 1 else 0) +
        (if 0 < (s.nodes x).ppar then 1 else 0) := by
      rcases h5 with h | h | h <;> simp [Nat.pos_of_ne_zero h]
    simp [h3, h4, this, show 0 < x by omega, h2]

/-- The procedures find-ready calls. -/
structure FindProcs {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} {S : PayloadSteps w p P Lay ok} {L : LazyProcs w p P Lay ok S}
    {Q : SplayProcs L} (E : ExposeProcs Q) {rs : σ → Bool} {rv : α → Bool}
    (T : ReadyTests w p Lay rs rv) where
  desc : ℕ
  pop : ℕ
  find : ℕ
  desc_body : p.procs[desc]? = some (descendBody desc L.pushDown T.sumTest T.valTest)
  pop_body : p.procs[pop]? = some popBody
  find_body : p.procs[find]? = some (findReadyBody find desc E.expose T.sumTest pop)

/-- The run of `findReadyBody`, on the stack `R` listed from the top down. -/
theorem findReadyBody_runs {w nb cap heap : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program} {rs : σ → Bool}
    {rv : α → Bool} {S : PayloadSteps w p P Lay ok} {L : LazyProcs w p P Lay ok S}
    {Q : SplayProcs L} {E : ExposeProcs Q} {T : ReadyTests w p Lay rs rv} (F : FindProcs E T)
    (ω : ℕ → Bool) {st : LctState α σ τ}
    (hptr : PtrOk cap st.splay) (hn : 2 * st.n + 1 < 2 ^ w) (hnb : 2 * cap + 3 ≤ nb) :
    ∀ (R : List ℕ) (pos : ℕ) {mem : ℕ → ℕ},
    Lay.NodesAt mem nb cap st.splay → HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem →
    IdxAt mem nb cap R.reverse → FindOk ok P rs rv st R →
    ∃ o st' c, Runs w p ω (findReadyBody F.find F.desc E.expose T.sumTest F.pop)
        (startState [nb, 2 * st.n + 1, heap] mem pos) o st' c ∧
      (o.value = (findLoop P rs rv st R).2.2 ∧
        Lay.NodesAt st'.mem nb cap (findLoop P rs rv st R).1.splay ∧
        IdxFrame Lay nb cap heap mem st'.mem (findLoop P rs rv st R).2.1) ∧
      0 + c ≤ findCost S T st R
  | [], pos, mem, hnodes, hheap, hI, _ => by
    have hwide := hheap.wide
    have hnh := hheap.nb_le
    have hroom := hheap.room
    have htop : mem (nb - 1) = 0 := by rw [hI.top]; rfl
    unfold findReadyBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step; try dsimp only
    rw [htop]
    wram_step
    · wram_step
      · exact ⟨by simp [findLoop, Outcome.value], by simpa [findLoop] using hnodes,
          IdxFrame.refl hheap.zero (by simpa [findLoop] using hI)⟩
      · simp only [findCost]; wram_cost
  | x :: R, pos, mem, hnodes, hheap, hI, hok => by
    have hwide := hheap.wide
    have hnh := hheap.nb_le
    have hroom := hheap.room
    have hS := hheap.stride_lt
    have hS6 := Lay.stride_pos
    rw [List.reverse_cons] at hI
    have hlen := hI.length_le
    rw [List.length_append, List.length_singleton, List.length_reverse] at hlen
    have hx : x ≤ cap := hI.le x (by simp)
    have htop : mem (nb - 1) = R.length + 1 := by rw [hI.top]; simp
    have hslot : mem (nb - (R.length + 1 + (R.length + 1) + 1)) = x := by
      have := hI.slot R.length (by simp)
      unfold slotAddr at this
      rw [show nb - (R.length + 1 + (R.length + 1) + 1) = nb - (2 * R.length + 3) by omega, this]
      simp
    have hA := hheap.addr_lt hx
    have hxS : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
    obtain ⟨hm0, hm1, hm2, hm3, -, -, hvx, hsx, -⟩ := hnodes x hx
    unfold nodeAddr at hA hm0 hm1 hm2 hm3 hsx hvx
    simp only [NodeLayout.OFF_LEFT, NodeLayout.OFF_RIGHT, NodeLayout.OFF_PAR, NodeLayout.OFF_PPAR,
      Nat.add_zero] at hm0 hm1 hm2 hm3
    have hoffS : Lay.offSum + Lay.sumW ≤ Lay.nodeStride := by unfold offSum nodeStride; omega
    unfold findReadyBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step; try dsimp only
    rw [htop]
    wram_step
    wram_step; try dsimp only
    rw [hslot]
    wram_step; try dsimp only
    have hsum_ok := T.sum_ok
    wram_step
    all_goals try omega
    all_goals try (intro v hv; simp only [List.mem_singleton] at hv; subst hv; omega)
    · exact ⟨_, _, _, rfl, by omega, hvx, hsx⟩
    rintro v₁ mem₁ pos₁ ⟨hmem₁, hres₁⟩
    subst mem₁
    have hv₁ : v₁ = if rs (st.splay.nodes x).sum then 1 else 0 := hres₁ _ hsx
    subst hv₁
    have hFn : 2 * st.n + 1 - 1 = 2 * st.n := by omega
    refine runs_cond_le (by eval_expr; all_goals (split_ifs <;> omega)) ?_ ?_
    · -- the top entry is valid
      intro hne
      have hvalid : ValidG rs st.n st.splay x := by
        rw [← validG_val_iff]
        simpa [hm0, hm1, hm2, hm3] using hne
      have hloop : findLoop P rs rv st (x :: R) =
          (lctExpose P (descState P rs rv st x) (descNode P rs rv st x),
            exposeNotes P (descState P rs rv st x) (descNode P rs rv st x) (x :: R).reverse,
            descNode P rs rv st x) := by
        simp [findLoop, hvalid]
      have hcost : findCost S T st (x :: R) =
          (descendSteps P rs rv st.splay (2 * st.n + 1) x + 1) *
            (pushDownCost S + 2 * T.cost + 120) +
            exposeCost S (descState P rs rv st x) (descNode P rs rv st x) + T.cost + 300 := by
        simp [findCost, hvalid]
      have hok' : DescendOk ok P rs rv st.splay (2 * st.n + 1) x ∧
          ExposeOk ok P (descState P rs rv st x) (descNode P rs rv st x) := by
        simpa [FindOk, hvalid] using hok
      rw [hloop, hcost]
      set D := descState P rs rv st x with hD
      set y := descNode P rs rv st x with hy
      have hpD := descend_ptr (P := P) (rs := rs) (rv := rv) (2 * st.n + 1) x hptr hx
      refine runs_seq_callBody_le F.desc_body (by eval_expr)
        (R := fun v m₁ c₁ => v = y ∧ Lay.NodesAt m₁.mem nb cap D.splay ∧
          TreeFrame Lay nb cap heap mem m₁.mem ∧
          c₁ ≤ (descendSteps P rs rv st.splay (2 * st.n + 1) x + 1) *
            (pushDownCost S + 2 * T.cost + 120)) ?_ ?_
      · obtain ⟨o, st', c, hr, ⟨hv, hn', hf⟩, hc⟩ := descendBody_runs L T F.desc_body ω
          (2 * st.n + 1) x _ hnodes hptr hx hheap hn hok'.1
        exact ⟨o, st', c, by simpa using hr, hv, hn', hf, by omega⟩
      rintro v₂ m₁ c₁ ⟨rfl, hn₁, hf₁, hc₁⟩
      have hheap₁ : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) m₁.mem :=
        ⟨hheap.rec_le, hroom, hf₁.1, hwide⟩
      have hI₁ := hI.of_treeFrame hnb hnh hf₁
      rw [← List.reverse_cons] at hI₁
      refine runs_seq_callBody_le E.expose_body (by eval_expr)
        (R := fun _ m₂ c₂ => Lay.NodesAt m₂.mem nb cap (lctExpose P D y).splay ∧
          IdxFrame Lay nb cap heap m₁.mem m₂.mem (exposeNotes P D y (x :: R).reverse) ∧
          c₂ ≤ exposeCost S D y) ?_ ?_
      · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ : ∃ o st' c, Runs w p ω
            (exposeBody Q.splay E.detachRight E.loop)
            (startState [nb, y, 2 * st.n + 1, heap] m₁.mem m₁.pos) o st' c ∧
            (Lay.NodesAt st'.mem nb cap (lctExpose P D y).splay ∧
              IdxFrame Lay nb cap heap m₁.mem st'.mem (exposeNotes P D y (x :: R).reverse)) ∧
            0 + c ≤ exposeCost S D y :=
          exposeBody_runs E ω (st := D) (pos := m₁.pos) hn₁ hpD.1 hpD.2 hheap₁ hn hok'.2 hnb hI₁
        exact ⟨o, st', c, hr, hn', hf, by omega⟩
      rintro - m₂ c₂ ⟨hn₂, hf₂, hc₂⟩
      wram_step
      · refine ⟨by simp [Outcome.value], hn₂, ?_⟩
        have hIx : IdxAt mem nb cap (x :: R).reverse := by rw [List.reverse_cons]; exact hI
        exact (IdxFrame.of_treeFrame hIx hnb hnh hf₁).trans hf₂
      · simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
          argsSize_cons, argsSize_nil, sumTestContract, recAddr] at *
        omega
    · -- the top entry is not valid: pop it and go on
      intro h0
      have hvalid : ¬ ValidG rs st.n st.splay x := by
        rw [← validG_val_iff]
        simpa [hm0, hm1, hm2, hm3] using h0
      have hloop : findLoop P rs rv st (x :: R) = findLoop P rs rv st R := by
        simp [findLoop, hvalid]
      have hcost : findCost S T st (x :: R) = T.cost + 300 + findCost S T st R := by
        simp [findCost, hvalid]
      have hok' : FindOk ok P rs rv st R := by simpa [FindOk, hvalid] using hok
      rw [hloop, hcost]
      refine runs_seq_callBody_le F.pop_body (by eval_expr)
        (R := fun _ m₁ c₁ => IdxAt m₁.mem nb cap R.reverse ∧
          (∀ a, ¬ InIndex nb cap a → m₁.mem a = mem a) ∧ c₁ ≤ 40) ?_ ?_
      · obtain ⟨o, st', c, hr, ⟨-, hI', hf⟩, hc⟩ := popBody_runs (w := w) (p := p) ω (pos := pos₁) hI hnb
          (by omega)
        exact ⟨o, st', c, by simpa using hr, hI', hf, by omega⟩
      rintro - m₁ c₁ ⟨hI₁, hf₁, hc₁⟩
      have hn₁ : Lay.NodesAt m₁.mem nb cap st.splay :=
        hnodes.congr Lay fun a ha => hf₁ a fun hi => not_inRecords_of_inIndex hi ha
      have hz₁ : ZeroFrom m₁.mem heap := fun a ha => by
        rw [hf₁ a fun hi => by have := hi.2; omega]; exact hheap.zero a ha
      have hheap₁ : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) m₁.mem :=
        ⟨hheap.rec_le, hroom, hz₁, hwide⟩
      refine runs_seq_callBody_le F.find_body (by eval_expr)
        (R := fun v m₂ c₂ => v = (findLoop P rs rv st R).2.2 ∧
          Lay.NodesAt m₂.mem nb cap (findLoop P rs rv st R).1.splay ∧
          IdxFrame Lay nb cap heap m₁.mem m₂.mem (findLoop P rs rv st R).2.1 ∧
          c₂ ≤ findCost S T st R) ?_ ?_
      · obtain ⟨o, st', c, hr, ⟨hv, hn', hf⟩, hc⟩ :=
          findReadyBody_runs F ω hptr hn hnb R m₁.pos hn₁ hheap₁ hI₁ hok'
        exact ⟨o, st', c, by simpa using hr, hv, hn', hf, by omega⟩
      rintro v₂ m₂ c₂ ⟨hv₂, hn₂, hf₂, hc₂⟩
      wram_step
      · refine ⟨by simp [Outcome.value, hv₂], hn₂, ?_⟩
        have hfr : TreeFrameN Lay nb cap heap mem m₁.mem :=
          ⟨hz₁, fun a _ _ hi => hf₁ a hi⟩
        exact ⟨hfr.trans hf₂.1, hf₂.2⟩
      · simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
          argsSize_cons, argsSize_nil, sumTestContract, recAddr] at *
        omega

end MinCostFlow.LinkCut.Gen
