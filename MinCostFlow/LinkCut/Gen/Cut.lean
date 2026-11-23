module

public import MinCostFlow.LinkCut.Gen.Link

/-!
# `cut` as a program

`cutBody` is the machine version of `lctCut`. It reroots at `u` and exposes `v`. If the exposed
tree has exactly three nodes, it finds the edge slot `ne` between `u` and `v` as the model does,
splays `ne`, splits the tree into three singletons, and pushes `ne` on the free list. The stored
size is `min sz 4`, so the test `sz = 3` reads it exactly.

The states of the model inside `lctCut` get names here: `cutMid` (after reroot and expose),
`cutPd` (after the push at the left child `cutL0` of `v`), and the slot `cutNe`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout MinCostFlow.LinkCut

variable {α σ τ : Type*}

section Model

variable (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ)

/-- The state of `lctCut P st u v` after the reroot at `u` and the expose of `v`. -/
def cutMid : LctState α σ τ := (lctPathSummary P st u v).1

/-- The left child of `v` after `cutMid`. -/
def cutL0 : ℕ := ((cutMid P st u v).splay.nodes v).left

/-- The splay state after the push at `cutL0`. -/
def cutPd : SplayState α σ τ := SplayState.pushDown P (cutMid P st u v).splay (cutL0 P st u v)

/-- The right child of `cutL0` after the push. -/
def cutR0 : ℕ := ((cutPd P st u v).nodes (cutL0 P st u v)).right

/-- The candidate for `u`. -/
def cutUc : ℕ :=
  if cutR0 P st u v = 0 then ((cutPd P st u v).nodes (cutL0 P st u v)).left else cutL0 P st u v

/-- The edge slot to remove. -/
def cutNe : ℕ := if cutR0 P st u v = 0 then cutL0 P st u v else cutR0 P st u v

theorem cutMid_n : (cutMid P st u v).n = st.n := rfl

theorem cutMid_freeHead : (cutMid P st u v).freeHead = st.freeHead := by
  show (lctExpose P (lctReroot P st u) v).freeHead = st.freeHead
  rw [lctExpose_freeHead, lctReroot_freeHead]

end Model

section Eqs

variable {P : LctPayload α σ τ} {st : LctState α σ τ} {u v : ℕ}

theorem lctCut_guard (h : u = 0 ∨ v = 0 ∨ u = v ∨ st.n < u ∨ st.n < v) :
    lctCut P st u v = st := by
  unfold lctCut lctCutCost
  rw [if_pos (by simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]; tauto)]

theorem lctCut_open (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (hnu : u ≤ st.n) (hnv : v ≤ st.n) :
    lctCut P st u v =
      if ((cutMid P st u v).splay.nodes v).sz ≠ 3 then cutMid P st u v
      else if cutUc P st u v ≠ u then { cutMid P st u v with splay := cutPd P st u v }
      else
        { n := st.n,
          splay := (SplayState.detachRootChildren P (SplayState.splay P (cutPd P st u v)
            (2 * st.n + 1) (cutNe P st u v)) (cutNe P st u v)).setPar (cutNe P st u v)
            st.freeHead,
          freeHead := cutNe P st u v } := by
  have hf := cutMid_freeHead P st u v
  unfold lctCut lctCutCost
  rw [if_neg (by simp [hu, hv, huv]; omega)]
  dsimp only
  rw [show (lctExposeCost P (lctRerootCost P st u).1 v).1 = cutMid P st u v from rfl]
  by_cases hsz : ((cutMid P st u v).splay.nodes v).sz = 3
  · simp only [bne_iff_ne, ne_eq, hsz, not_true_eq_false, if_false]
    by_cases hr : cutR0 P st u v = 0
    · simp only [cutUc, cutNe, cutR0, cutPd, cutL0] at hr ⊢
      simp only [hr, beq_self_eq_true, if_true, hf]
      split_ifs <;> rfl
    · simp only [cutUc, cutNe, cutR0, cutPd, cutL0] at hr ⊢
      simp only [hr, beq_iff_eq, if_false, hf]
      split_ifs <;> rfl
  · simp only [bne_iff_ne, ne_eq, hsz, not_false_eq_true, if_true]

end Eqs

/-! ### The program -/

/-- `pick [c, a, b]` returns `a` if `c ≠ 0` and `b` if `c = 0`. -/
def pickBody : Stmt := .cond (.reg 0) (.ret (.reg 1)) (.ret (.reg 2))

theorem pickBody_noRand : pickBody.NoRand := by simp [pickBody, Stmt.NoRand]

theorem pickBody_runs {w : ℕ} {p : Program} (ω : ℕ → Bool) (c a b : ℕ) (mem : ℕ → ℕ)
    (pos : ℕ) : ∃ o st' k, Runs w p ω pickBody (startState [c, a, b] mem pos) o st' k ∧
      (o.value = (if c = 0 then b else a) ∧ st'.mem = mem) ∧ 0 + k ≤ 5 := by
  unfold pickBody
  rw [startState]
  wram_step
  · wram_step
    · simp [Outcome.value, hcond]
    · wram_cost
  · wram_step
    · simp [Outcome.value, hcond]
    · wram_cost

/-- The end of `cutBody`: if the candidate in register `11` is `u`, cut out the slot in
register `12`. -/
def cutTail (splayProc dcProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 11) (.reg 2))
    (.call 7 splayProc [.reg 0, .reg 12, .reg 6, .reg 5] ;;
     .call 7 dcProc [.reg 0, .reg 12, .reg 5] ;;
     .store (.bin .add (recAddr 12) (.const 2)) (.load (.reg 1)) ;;
     .store (.reg 1) (.reg 12) ;;
     .ret (.const 0))
    (.ret (.const 0))

/-- `lctCut` on `[nb, fh, u, v, n, heap]`. -/
def cutBody (reProc pdProc splayProc dcProc pickProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 0))
  (.cond (.bin .eq (.reg 3) (.const 0)) (.ret (.const 0))
  (.cond (.bin .eq (.reg 2) (.reg 3)) (.ret (.const 0))
  (.cond (.bin .lt (.reg 4) (.reg 2)) (.ret (.const 0))
  (.cond (.bin .lt (.reg 4) (.reg 3)) (.ret (.const 0))
  (.assign 6 (.bin .add (.bin .mul (.const 2) (.reg 4)) (.const 1)) ;;
   .call 7 reProc [.reg 0, .reg 2, .reg 3, .reg 6, .reg 5] ;;
   .assign 8 (recAddr 3) ;;
   .cond (.bin .eq (.load (.bin .add (.reg 8) (.const 4))) (.const 3))
    (.assign 9 (.load (.reg 8)) ;;
     .call 7 pdProc [.reg 0, .reg 9, .reg 5] ;;
     .assign 10 (.load (.bin .add (recAddr 9) (.const 1))) ;;
     .call 11 pickProc [.reg 10, .reg 9, .load (recAddr 9)] ;;
     .call 12 pickProc [.reg 10, .reg 10, .reg 9] ;;
     cutTail splayProc dcProc)
    (.ret (.const 0)))))))

theorem cutBody_noRand (a b c d e : ℕ) :
    (cutBody a b c d e).NoRand := by
  simp [cutBody, cutTail, recAddr, Stmt.NoRand]

/-- The payload values of `lctCut P st u v` are representable. -/
def CutOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) :
    Prop :=
  RerootExposeOk ok P st u v ∧
  (((cutMid P st u v).splay.nodes v).sz = 3 →
    PushDownOk ok P (cutMid P st u v).splay (cutL0 P st u v)) ∧
  (((cutMid P st u v).splay.nodes v).sz = 3 → cutUc P st u v = u →
    SplayOk ok P (cutPd P st u v) (2 * st.n + 1) (cutNe P st u v) ∧
    DetachChildrenOk ok P (SplayState.splay P (cutPd P st u v) (2 * st.n + 1) (cutNe P st u v))
      (cutNe P st u v))

/-- The splay of the slot inside a cut, charged only when the cut splays it. -/
def cutSplayCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) (st : LctState α σ τ) (u v : ℕ) : ℕ :=
  if ((cutMid P st u v).splay.nodes v).sz = 3 ∧ cutUc P st u v = u then
    splayCost S (cutPd P st u v) (2 * st.n + 1) (cutNe P st u v)
  else 0

/-- The cost bound of `lctCut P st u v`. -/
def cutCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) (st : LctState α σ τ) (u v : ℕ) : ℕ :=
  if u = 0 ∨ v = 0 ∨ u = v ∨ st.n < u ∨ st.n < v then 1000
  else rerootExposeCost S st u v + pushDownCost S + cutSplayCost S st u v + S.cost + 1000

/-- The nodes `lctCut P st u v` notes: those of the reroot and expose, then those of
`detachRootChildren`. -/
def cutNotes (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) (I : List ℕ) : List ℕ :=
  if u = 0 ∨ v = 0 ∨ u = v ∨ st.n < u ∨ st.n < v then I
  else if ((cutMid P st u v).splay.nodes v).sz = 3 ∧ cutUc P st u v = u then
    dcNotes (SplayState.splay P (cutPd P st u v) (2 * st.n + 1) (cutNe P st u v))
      (cutNe P st u v) (rerootExposeNotes P st u v I)
  else rerootExposeNotes P st u v I

variable {w nb cap heap : ℕ} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
  {ok : PayloadOk α σ τ} {p : Program} {S : PayloadSteps w p P Lay ok}
  {L : LazyProcs w p P Lay ok S} {Q : SplayProcs L} {E : ExposeProcs Q}

/-- The run of `cutBody`. The free list word `fh` lies outside the records and below the heap
pointer. -/
theorem cutBody_runs (R : PathProcs E) {dc pk : ℕ}
    (hdc : p.procs[dc]? = some (detachRootChildrenBody Q.pull E.note))
    (hpk : p.procs[pk]? = some pickBody) (ω : ℕ → Bool)
    {fh u v pos : ℕ} {mem : ℕ → ℕ} {st : LctState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st.splay) (hfh : mem fh = st.freeHead)
    (hptr : PtrOk cap st.splay) (hncap : st.n ≤ cap)
    (hheap : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem)
    (hfr : ¬ Lay.InRecords nb cap fh) (hfi : ¬ InIndex nb cap fh) (hfh' : fh < heap)
    (hn : 2 * st.n + 1 < 2 ^ w) (hok : CutOk ok P st u v)
    (hnb : 2 * cap + 3 ≤ nb) {I : List ℕ} (hI : IdxAt mem nb cap I) :
    ∃ o st' c, Runs w p ω (cutBody R.rerootExpose L.pushDown Q.splay dc pk)
        (startState [nb, fh, u, v, st.n, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (lctCut P st u v).splay ∧
        st'.mem fh = (lctCut P st u v).freeHead ∧ LinkFrame Lay nb cap fh heap mem st'.mem ∧
        IdxAt st'.mem nb cap (cutNotes P st u v I)) ∧
      0 + c ≤ cutCost S st u v := by
  have hnh := hheap.nb_le
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS := hheap.stride_lt
  have hS6 := Lay.stride_pos
  have hrec := hheap.rec_le
  have hlt : ∀ y ≤ cap, nb + Lay.nodeStride * y + Lay.nodeStride ≤ heap := fun y hy => by
    have := hheap.addr_lt hy; unfold nodeAddr at this; exact this
  have hyS : ∀ y, y ≤ Lay.nodeStride * y := fun y => Nat.le_mul_of_pos_left y (by omega)
  have hsame : ∀ m : ℕ → ℕ, TreeFrameN Lay nb cap heap mem m → m fh = mem fh :=
    fun m hm => hm.2 fh hfh' hfr hfi
  have htriv : ∀ (m : State), m.mem = mem →
      (u = 0 ∨ v = 0 ∨ u = v ∨ st.n < u ∨ st.n < v) →
      (Lay.NodesAt m.mem nb cap st.splay ∧ m.mem fh = st.freeHead ∧
        LinkFrame Lay nb cap fh heap mem m.mem ∧ IdxAt m.mem nb cap (cutNotes P st u v I)) :=
    fun m hm hg => by
      rw [hm]
      exact ⟨hnodes, hfh, ⟨hheap.zero, fun _ _ _ _ _ => rfl⟩, by simpa [cutNotes, hg] using hI⟩
  have htree : ∀ (m : ℕ → ℕ) (s : LctState α σ τ) (J : List ℕ), Lay.NodesAt m nb cap s.splay →
      IdxFrame Lay nb cap heap mem m J → s.freeHead = st.freeHead → J = cutNotes P st u v I →
      (Lay.NodesAt m nb cap s.splay ∧ m fh = s.freeHead ∧ LinkFrame Lay nb cap fh heap mem m ∧
        IdxAt m nb cap (cutNotes P st u v I)) :=
    fun m s J hm hf hfs hJ => ⟨hm, by rw [hsame m hf.1, hfh, hfs], hf.1.linkFrame, hJ ▸ hf.2⟩
  obtain ⟨ok₁, ok₂, ok₃⟩ := hok
  unfold cutBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · rw [lctCut_guard (Or.inl hcond)]
    wram_step
    · exact htriv _ rfl (Or.inl hcond)
    · rw [cutCost, if_pos (Or.inl hcond)]; wram_cost
  have hu0 : u ≠ 0 := hcond
  wram_step
  · rw [lctCut_guard (Or.inr (Or.inl hcond))]
    wram_step
    · exact htriv _ rfl (Or.inr (Or.inl hcond))
    · rw [cutCost, if_pos (Or.inr (Or.inl hcond))]; wram_cost
  have hv0 : v ≠ 0 := hcond
  wram_step
  · rw [lctCut_guard (Or.inr (Or.inr (Or.inl hcond)))]
    wram_step
    · exact htriv _ rfl (Or.inr (Or.inr (Or.inl hcond)))
    · rw [cutCost, if_pos (Or.inr (Or.inr (Or.inl hcond)))]; wram_cost
  have huv : u ≠ v := hcond
  wram_step
  · rw [lctCut_guard (Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hcond)))))]
    wram_step
    · exact htriv _ rfl (Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hcond)))))
    · rw [cutCost, if_pos (Or.inr (Or.inr (Or.inr (Or.inl (by simpa using hcond)))))]; wram_cost
  have hnu : u ≤ st.n := by simpa using hcond
  wram_step
  · rw [lctCut_guard (Or.inr (Or.inr (Or.inr (Or.inr (by simpa using hcond)))))]
    wram_step
    · exact htriv _ rfl (Or.inr (Or.inr (Or.inr (Or.inr (by simpa using hcond)))))
    · rw [cutCost, if_pos (Or.inr (Or.inr (Or.inr (Or.inr (by simpa using hcond)))))]; wram_cost
  have hnv : v ≤ st.n := by simpa using hcond
  have hu : u ≤ cap := by omega
  have hv : v ≤ cap := by omega
  have hg : ¬ (u = 0 ∨ v = 0 ∨ u = v ∨ st.n < u ∨ st.n < v) := by omega
  rw [lctCut_open hu0 hv0 huv hnu hnv]
  wram_step; try dsimp only
  -- reroot at `u`, expose `v`
  refine runs_seq_callBody_le R.rerootExpose_body (by eval_expr)
    (R := fun _ m₁ c₁ => Lay.NodesAt m₁.mem nb cap (cutMid P st u v).splay ∧
      IdxFrame Lay nb cap heap mem m₁.mem (rerootExposeNotes P st u v I) ∧
      c₁ ≤ rerootExposeCost S st u v) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := rerootExposeBody_runs R ω (pos := pos) hnodes hptr
      hu hv hheap hn ok₁ hnb hI
    exact ⟨o, st', c, by simpa using hr, hn', hf, by omega⟩
  rintro - m₁ c₁ ⟨hn₁, hf₁, hc₁⟩
  have hp₁ : PtrOk cap (cutMid P st u v).splay := (hptr.reroot hu).expose hv
  have hAv := hlt v hv
  have hyv := hyS v
  wram_step; try dsimp only
  have hm4 : m₁.mem (nb + Lay.nodeStride * v + 4) = min ((cutMid P st u v).splay.nodes v).sz 4 :=
    (hn₁ v hv).2.2.2.2.1
  have hsz3 : (min ((cutMid P st u v).splay.nodes v).sz 4 = 3) ↔
      ((cutMid P st u v).splay.nodes v).sz = 3 := by omega
  wram_step
  swap
  · -- the size is not `3`
    have hsz : ((cutMid P st u v).splay.nodes v).sz ≠ 3 := fun h =>
      hcond (by rw [hm4, hsz3]; exact h)
    rw [if_pos hsz]
    wram_step
    · exact htree _ _ _ hn₁ hf₁ (cutMid_freeHead P st u v) (by simp [cutNotes, hg, hsz])
    · simp only [cutCost, if_neg hg]
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
        argsSize_cons, argsSize_nil] at *
      omega
  have hsz : ((cutMid P st u v).splay.nodes v).sz = 3 := by rw [← hsz3, ← hm4]; exact hcond
  rw [if_neg (not_not.mpr hsz)]
  wram_step; try dsimp only
  have hm0 : m₁.mem (nb + Lay.nodeStride * v) = cutL0 P st u v := (hn₁ v hv).1
  rw [hm0]
  have hl0c : cutL0 P st u v ≤ cap := (hp₁ v hv).1
  -- push at the left child of `v`
  refine runs_seq_callBody_le L.pushDown_body (by eval_expr)
    (R := fun _ m₂ c₂ => Lay.NodesAt m₂.mem nb cap (cutPd P st u v) ∧
      IdxFrame Lay nb cap heap mem m₂.mem (rerootExposeNotes P st u v I) ∧
      c₂ ≤ pushDownCost S) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := pushDownBody_runs L ω (pos := m₁.pos) hn₁ hp₁ hl0c
      ⟨hrec, hroom, hf₁.1.1, hwide⟩ (ok₂ hsz)
    exact ⟨o, st', c, by simpa using hr, hn', hf₁.trans_tree hnb hnh hf, by omega⟩
  rintro - m₂ c₂ ⟨hn₂, hf₂, hc₂⟩
  have hp₂ : PtrOk cap (cutPd P st u v) := hp₁.pushDown hl0c
  have hAl := hlt _ hl0c
  have hyl := hyS (cutL0 P st u v)
  have hm1' : m₂.mem (nb + Lay.nodeStride * cutL0 P st u v + 1) = cutR0 P st u v :=
    (hn₂ _ hl0c).2.1
  have hm0' : m₂.mem (nb + Lay.nodeStride * cutL0 P st u v) =
      ((cutPd P st u v).nodes (cutL0 P st u v)).left := (hn₂ _ hl0c).1
  have hr0c : cutR0 P st u v ≤ cap := (hp₂ _ hl0c).2.1
  have hlc : ((cutPd P st u v).nodes (cutL0 P st u v)).left ≤ cap := (hp₂ _ hl0c).1
  have hyr := hyS (cutR0 P st u v)
  have hAr := hlt _ hr0c
  wram_step; try dsimp only
  rw [hm1']
  -- the candidate and the slot
  refine runs_seq_callBody_le hpk (by eval_expr)
    (R := fun x m₃ c₃ => x = cutUc P st u v ∧ m₃.mem = m₂.mem ∧ c₃ ≤ 5) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hv', hm'⟩, hc⟩ := pickBody_runs (w := w) (p := p) ω (cutR0 P st u v)
      (cutL0 P st u v) ((cutPd P st u v).nodes (cutL0 P st u v)).left m₂.mem m₂.pos
    refine ⟨o, st', c, by simpa [hm0'] using hr, ?_, hm', by omega⟩
    rw [hv', cutUc]
  rintro x₃ m₃ c₃ ⟨hx₃, hm₃, hc₃⟩
  refine runs_seq_callBody_le hpk (by eval_expr)
    (R := fun x m₄ c₄ => x = cutNe P st u v ∧ m₄.mem = m₂.mem ∧ c₄ ≤ 5) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hv', hm'⟩, hc⟩ := pickBody_runs (w := w) (p := p) ω (cutR0 P st u v)
      (cutR0 P st u v) (cutL0 P st u v) m₃.mem m₃.pos
    refine ⟨o, st', c, by simpa using hr, ?_, hm'.trans hm₃, by omega⟩
    rw [hv', cutNe]
  rintro x₄ m₄ c₄ ⟨hx₄, hm₄, hc₄⟩
  subst hx₃ hx₄
  have hnec : cutNe P st u v ≤ cap := by unfold cutNe; split_ifs <;> assumption
  have hyn := hyS (cutNe P st u v)
  have hAn := hlt _ hnec
  -- the end
  unfold cutTail
  refine runs_cond_le (by eval_expr) ?_ ?_
  swap
  · intro hc
    have huc : cutUc P st u v ≠ u := by intro h; simp [h] at hc
    rw [if_pos huc]
    wram_step
    · rw [hm₄]
      exact htree _ _ _ hn₂ hf₂ (cutMid_freeHead P st u v) (by simp [cutNotes, hg, huc])
    · simp only [cutCost, if_neg hg]
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
        argsSize_cons, argsSize_nil] at *
      omega
  intro hc
  have huc : cutUc P st u v = u := by by_contra h; simp [h] at hc
  rw [if_neg (not_not.mpr huc)]
  obtain ⟨okS, okD⟩ := ok₃ hsz huc
  set s₅ := SplayState.splay P (cutPd P st u v) (2 * st.n + 1) (cutNe P st u v) with hs₅
  refine runs_seq_callBody_le Q.splay_body (by eval_expr)
    (R := fun _ m₅ c₅ => Lay.NodesAt m₅.mem nb cap s₅ ∧
      IdxFrame Lay nb cap heap mem m₅.mem (rerootExposeNotes P st u v I) ∧
      c₅ ≤ splayCost S (cutPd P st u v) (2 * st.n + 1) (cutNe P st u v)) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := splayBody_runs Q ω (pos := m₄.pos)
      (mem := m₄.mem) (by rw [hm₄]; exact hn₂) hp₂ hnec
      ⟨hrec, hroom, by rw [hm₄]; exact hf₂.1.1, hwide⟩ hn okS
    refine ⟨o, st', c, by simpa using hr, hn', ?_, by omega⟩
    rw [hm₄] at hf; exact hf₂.trans_tree hnb hnh hf
  rintro - m₅ c₅ ⟨hn₅, hf₅, hc₅⟩
  refine runs_seq_callBody_le hdc (by eval_expr)
    (R := fun _ m₆ c₆ =>
      Lay.NodesAt m₆.mem nb cap (SplayState.detachRootChildren P s₅ (cutNe P st u v)) ∧
      IdxFrame Lay nb cap heap mem m₆.mem
        (dcNotes s₅ (cutNe P st u v) (rerootExposeNotes P st u v I)) ∧
      c₆ ≤ S.cost + 600) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := detachRootChildrenBody_runs S Q.pull_body E.note_body
      ω (pos := m₅.pos) hn₅ (hp₂.splay hnec) hnec ⟨hrec, by omega, hf₅.1.1, hwide⟩ okD hnb hf₅.2
    exact ⟨o, st', c, by simpa using hr, hn', hf₅.trans hf, by omega⟩
  rintro - m₆ c₆ ⟨hn₆, hf₆, hc₆⟩
  have hm₆ : m₆.mem fh = st.freeHead := by rw [hsame _ hf₆.1, hfh]
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₇ hM₇ => ?_
  rw [hm₆] at hM₇
  have h₇ : Lay.NodesAt M₇ nb cap ((SplayState.detachRootChildren P s₅ (cutNe P st u v)).setPar
      (cutNe P st u v) st.freeHead) ∧ TreeFrame Lay nb cap heap m₆.mem M₇ := by
    rw [hM₇]; exact NodesAt.ctrl hn₆ (TreeFrame.refl hf₆.1.1) hnec (by decide)
      (hheap.addr_lt hnec) (fun h => h.setPar Lay hnec)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₈ hM₈ => ?_
  wram_step
  · dsimp only
    refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · rw [hM₈]
      exact h₇.1.congr Lay fun a ha => Function.update_of_ne (by rintro rfl; exact hfr ha) _ _
    · rw [hM₈]; simp only [Function.update_self]
    · intro a ha
      rw [hM₈, Function.update_of_ne (by omega)]; exact h₇.2.1 a ha
    · intro a ha hr hi hafh
      rw [hM₈, Function.update_of_ne hafh]; dsimp only; rw [h₇.2.2 a ha hr]
      exact hf₆.1.2 a ha hr hi
    · have hI₇ := hf₆.2.of_treeFrame hnb hnh h₇.2
      rw [show cutNotes P st u v I =
          dcNotes s₅ (cutNe P st u v) (rerootExposeNotes P st u v I) by
        simp [cutNotes, hg, hsz, huc, hs₅]]
      refine hI₇.congr hnb fun a ha => ?_
      rw [hM₈, Function.update_of_ne]; rintro rfl; exact hfi ha
  · simp only [cutCost, if_neg hg, cutSplayCost, if_pos (And.intro hsz huc)]
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil] at *
    omega

end MinCostFlow.LinkCut.Gen
