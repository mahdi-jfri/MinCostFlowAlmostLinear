module

public import MinCostFlow.LinkCut.Gen.Expose
public import MinCostFlow.LinkCut.ForestModelSplice

/-!
# `reroot`, path apply and path summary as programs

`rerootBody` is the machine version of `lctReroot` (expose, then reverse the exposed node).
`rerootExposeBody` reroots at `u` and then exposes `v`; this is the state of `lctPathSummary`,
and the summary is then the summary of `v`. `pathApplyBody` does the same and then applies a
tag to `v`, as `lctPathApply`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-- `lctReroot` on `[nb, v, splayFuel, heap]`. -/
def rerootBody (exposeProc revProc : ℕ) : Stmt :=
  .call 4 exposeProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
  .call 4 revProc [.reg 0, .reg 1, .reg 3] ;;
  .ret (.const 0)

/-- Reroot at `u`, then expose `v`; on `[nb, u, v, splayFuel, heap]`. -/
def rerootExposeBody (rerootProc exposeProc : ℕ) : Stmt :=
  .call 5 rerootProc [.reg 0, .reg 1, .reg 3, .reg 4] ;;
  .call 5 exposeProc [.reg 0, .reg 2, .reg 3, .reg 4] ;;
  .ret (.const 0)

/-- `lctPathApply` on `[nb, u, v, b, splayFuel, heap]`, with the tag in the block at `b`. -/
def pathApplyBody (reProc applyProc : ℕ) : Stmt :=
  .call 6 reProc [.reg 0, .reg 1, .reg 2, .reg 4, .reg 5] ;;
  .call 6 applyProc [.reg 0, .reg 2, .reg 3, .reg 5] ;;
  .ret (.const 0)

theorem rerootBody_noRand (a b : ℕ) : (rerootBody a b).NoRand := by
  simp [rerootBody, Stmt.NoRand]

theorem rerootExposeBody_noRand (a b : ℕ) : (rerootExposeBody a b).NoRand := by
  simp [rerootExposeBody, Stmt.NoRand]

theorem pathApplyBody_noRand (a b : ℕ) : (pathApplyBody a b).NoRand := by
  simp [pathApplyBody, Stmt.NoRand]

/-- The procedures of this file, at their indices in the program. -/
structure PathProcs {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} {S : PayloadSteps w p P Lay ok} {L : LazyProcs w p P Lay ok S}
    {Q : SplayProcs L} (E : ExposeProcs Q) where
  reroot : ℕ
  rerootExpose : ℕ
  pathApply : ℕ
  reroot_body : p.procs[reroot]? = some (rerootBody E.expose L.revNode)
  rerootExpose_body : p.procs[rerootExpose]? = some (rerootExposeBody reroot E.expose)
  pathApply_body : p.procs[pathApply]? = some (pathApplyBody rerootExpose L.applyTag)

theorem lctReroot_splay (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    (lctReroot P st v).splay = SplayState.revNode P (lctExpose P st v).splay v := rfl

theorem lctReroot_n (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    (lctReroot P st v).n = st.n := rfl

theorem lctReroot_freeHead (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    (lctReroot P st v).freeHead = st.freeHead := lctExpose_freeHead P st v

theorem lctPathSummary_fst (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) :
    (lctPathSummary P st u v).1 = lctExpose P (lctReroot P st u) v := rfl

theorem lctPathSummary_snd (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) :
    (lctPathSummary P st u v).2 = ((lctExpose P (lctReroot P st u) v).splay.nodes v).sum := rfl

theorem lctPathApply_splay (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) (t : τ) :
    (lctPathApply P st u v t).splay =
      SplayState.applyTagNode P (lctExpose P (lctReroot P st u) v).splay v t := rfl

theorem lctPathApply_n (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) (t : τ) :
    (lctPathApply P st u v t).n = st.n := rfl

theorem lctPathApply_freeHead (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) (t : τ) :
    (lctPathApply P st u v t).freeHead = st.freeHead := by
  show (lctExpose P (lctReroot P st u) v).freeHead = st.freeHead
  rw [lctExpose_freeHead, lctReroot_freeHead]

theorem PtrOk.reroot {cap v : ℕ} {P : LctPayload α σ τ} {st : LctState α σ τ}
    (h : PtrOk cap st.splay) (hv : v ≤ cap) : PtrOk cap (lctReroot P st v).splay :=
  (h.expose hv).revNode hv

/-- The payload values of `lctReroot P st v` are representable. -/
def RerootOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : LctState α σ τ) (v : ℕ) :
    Prop :=
  ExposeOk ok P st v ∧ (v ≠ 0 → RevOk ok P ((lctExpose P st v).splay.nodes v))

/-- The payload values of `lctPathSummary P st u v` are representable. -/
def RerootExposeOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : LctState α σ τ)
    (u v : ℕ) : Prop :=
  RerootOk ok P st u ∧ ExposeOk ok P (lctReroot P st u) v

/-- The payload values of `lctPathApply P st u v t` are representable. -/
def PathApplyOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : LctState α σ τ)
    (u v : ℕ) (t : τ) : Prop :=
  RerootExposeOk ok P st u v ∧
    (v ≠ 0 → ActOk ok P t ((lctExpose P (lctReroot P st u) v).splay.nodes v))

/-- The cost bound of `lctReroot P st v`. -/
def rerootCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) (st : LctState α σ τ) (v : ℕ) : ℕ :=
  exposeCost S st v + S.cost + 100

/-- The cost bound of `lctPathSummary P st u v`. -/
def rerootExposeCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) (st : LctState α σ τ) (u v : ℕ) : ℕ :=
  rerootCost S st u + exposeCost S (lctReroot P st u) v + 100

variable {w nb cap heap : ℕ} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
  {ok : PayloadOk α σ τ} {p : Program} {S : PayloadSteps w p P Lay ok}
  {L : LazyProcs w p P Lay ok S} {Q : SplayProcs L} {E : ExposeProcs Q}

/-- The nodes `lctPathSummary P st u v` notes: those of the two exposes. -/
def rerootExposeNotes (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ)
    (S : List ℕ) : List ℕ :=
  exposeNotes P (lctReroot P st u) v (exposeNotes P st u S)

/-- The run of `rerootBody`. -/
theorem rerootBody_runs (ω : ℕ → Bool) {v pos : ℕ} {mem : ℕ → ℕ} {st : LctState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st.splay) (hptr : PtrOk cap st.splay) (hv : v ≤ cap)
    (hheap : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem)
    (hn : 2 * st.n + 1 < 2 ^ w) (hok : RerootOk ok P st v)
    (hnb : 2 * cap + 3 ≤ nb) {I : List ℕ} (hI : IdxAt mem nb cap I) :
    ∃ o st' c, Runs w p ω (rerootBody E.expose L.revNode)
        (startState [nb, v, 2 * st.n + 1, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (lctReroot P st v).splay ∧
        IdxFrame Lay nb cap heap mem st'.mem (exposeNotes P st v I)) ∧
      0 + c ≤ rerootCost S st v := by
  have hnh := hheap.nb_le
  have hroom := hheap.room
  have hwide := hheap.wide
  unfold rerootBody
  rw [startState]
  refine runs_seq_callBody_le E.expose_body (by eval_expr)
    (R := fun _ m₁ c₁ => Lay.NodesAt m₁.mem nb cap (lctExpose P st v).splay ∧
      IdxFrame Lay nb cap heap mem m₁.mem (exposeNotes P st v I) ∧ c₁ ≤ exposeCost S st v) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := exposeBody_runs E ω (pos := pos) hnodes hptr hv
      hheap hn hok.1 hnb hI
    exact ⟨o, st', c, by simpa using hr, hn', hf, by omega⟩
  rintro - m₁ c₁ ⟨hn₁, hf₁, hc₁⟩
  refine runs_seq_callBody_le L.revNode_body (by eval_expr)
    (R := fun _ m₂ c₂ => Lay.NodesAt m₂.mem nb cap (lctReroot P st v).splay ∧
      IdxFrame Lay nb cap heap mem m₂.mem (exposeNotes P st v I) ∧ c₂ ≤ S.cost + 70) ?_ ?_
  · obtain ⟨o, st', c, hr, hn', hf, hc⟩ := revNodeBody_runs S ω (pos := m₁.pos) hn₁ hv
      ⟨hheap.rec_le, by omega, hf₁.1.1, hwide⟩ hok.2
    exact ⟨_, st', c, by simpa using hr, hn', hf₁.trans_tree hnb hnh hf, hc⟩
  rintro - m₂ c₂ ⟨hn₂, hf₂, hc₂⟩
  wram_step
  · exact ⟨hn₂, hf₂⟩
  · simp only [rerootCost]
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil] at *
    omega

/-- The run of `rerootExposeBody`. -/
theorem rerootExposeBody_runs (R : PathProcs E) (ω : ℕ → Bool) {u v pos : ℕ} {mem : ℕ → ℕ}
    {st : LctState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st.splay) (hptr : PtrOk cap st.splay) (hu : u ≤ cap)
    (hv : v ≤ cap) (hheap : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem)
    (hn : 2 * st.n + 1 < 2 ^ w) (hok : RerootExposeOk ok P st u v)
    (hnb : 2 * cap + 3 ≤ nb) {I : List ℕ} (hI : IdxAt mem nb cap I) :
    ∃ o st' c, Runs w p ω (rerootExposeBody R.reroot E.expose)
        (startState [nb, u, v, 2 * st.n + 1, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (lctPathSummary P st u v).1.splay ∧
        IdxFrame Lay nb cap heap mem st'.mem (rerootExposeNotes P st u v I)) ∧
      0 + c ≤ rerootExposeCost S st u v := by
  have hroom := hheap.room
  have hwide := hheap.wide
  unfold rerootExposeBody
  rw [startState]
  refine runs_seq_callBody_le R.reroot_body (by eval_expr)
    (R := fun _ m₁ c₁ => Lay.NodesAt m₁.mem nb cap (lctReroot P st u).splay ∧
      IdxFrame Lay nb cap heap mem m₁.mem (exposeNotes P st u I) ∧ c₁ ≤ rerootCost S st u) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := rerootBody_runs (E := E) ω (pos := pos) hnodes hptr
      hu hheap hn hok.1 hnb hI
    exact ⟨o, st', c, by simpa using hr, hn', hf, by omega⟩
  rintro - m₁ c₁ ⟨hn₁, hf₁, hc₁⟩
  refine runs_seq_callBody_le E.expose_body (by eval_expr)
    (R := fun _ m₂ c₂ => Lay.NodesAt m₂.mem nb cap (lctPathSummary P st u v).1.splay ∧
      IdxFrame Lay nb cap heap mem m₂.mem (rerootExposeNotes P st u v I) ∧
      c₂ ≤ exposeCost S (lctReroot P st u) v) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := exposeBody_runs E ω (pos := m₁.pos) (st := lctReroot P st u)
      hn₁ (hptr.reroot hu) hv ⟨hheap.rec_le, hroom, hf₁.1.1, hwide⟩ hn hok.2 hnb hf₁.2
    exact ⟨o, st', c, by simpa [lctReroot_n] using hr, hn', hf₁.trans hf, by omega⟩
  rintro - m₂ c₂ ⟨hn₂, hf₂, hc₂⟩
  wram_step
  · exact ⟨hn₂, hf₂⟩
  · simp only [rerootExposeCost]
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil] at *
    omega

/-- The run of `pathApplyBody`. The tag block at `b` lies after the records and below the heap
pointer. -/
theorem pathApplyBody_runs (R : PathProcs E) (ω : ℕ → Bool) {u v b pos : ℕ} {t : τ}
    {mem : ℕ → ℕ} {st : LctState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st.splay) (hptr : PtrOk cap st.splay) (hu : u ≤ cap)
    (hv : v ≤ cap) (hheap : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem)
    (hb : Lay.nodeAddr nb (cap + 1) ≤ b) (hbh : b + Lay.tagW ≤ heap) (ht : Lay.TagAt mem b t)
    (hn : 2 * st.n + 1 < 2 ^ w) (hok : PathApplyOk ok P st u v t)
    (hnb : 2 * cap + 3 ≤ nb) {I : List ℕ} (hI : IdxAt mem nb cap I) :
    ∃ o st' c, Runs w p ω (pathApplyBody R.rerootExpose L.applyTag)
        (startState [nb, u, v, b, 2 * st.n + 1, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (lctPathApply P st u v t).splay ∧
        IdxFrame Lay nb cap heap mem st'.mem (rerootExposeNotes P st u v I)) ∧
      0 + c ≤ rerootExposeCost S st u v + S.cost + 100 := by
  have hroom := hheap.room
  have hwide := hheap.wide
  unfold pathApplyBody
  rw [startState]
  refine runs_seq_callBody_le R.rerootExpose_body (by eval_expr)
    (R := fun _ m₁ c₁ => Lay.NodesAt m₁.mem nb cap (lctPathSummary P st u v).1.splay ∧
      IdxFrame Lay nb cap heap mem m₁.mem (rerootExposeNotes P st u v I) ∧
      c₁ ≤ rerootExposeCost S st u v) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := rerootExposeBody_runs R ω (pos := pos) hnodes hptr
      hu hv hheap hn hok.1 hnb hI
    exact ⟨o, st', c, by simpa using hr, hn', hf, by omega⟩
  rintro - m₁ c₁ ⟨hn₁, hf₁, hc₁⟩
  have hnh := hheap.nb_le
  have hbnb : nb ≤ b := by have := hheap.rec_le; unfold nodeAddr at this; unfold nodeAddr at hb; omega
  have ht₁ : Lay.TagAt m₁.mem b t := Lay.tag_congr _ _ _ _ ht fun i hi => by
    refine hf₁.1.2 _ (by omega) (fun hr => ?_) fun hx => ?_
    · have := hr.2
      omega
    · have := hx.2
      omega
  refine runs_seq_callBody_le L.applyTag_body (by eval_expr)
    (R := fun _ m₂ c₂ => Lay.NodesAt m₂.mem nb cap (lctPathApply P st u v t).splay ∧
      IdxFrame Lay nb cap heap mem m₂.mem (rerootExposeNotes P st u v I) ∧
      c₂ ≤ S.cost + 30) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := applyTagBody_runs S ω (pos := m₁.pos) hn₁ hv
      ⟨hheap.rec_le, by omega, hf₁.1.1, hwide⟩ hb hbh ht₁ hok.2
    exact ⟨o, st', c, by simpa using hr, hn', hf₁.trans_tree hnb hnh hf, by omega⟩
  rintro - m₂ c₂ ⟨hn₂, hf₂, hc₂⟩
  wram_step
  · exact ⟨hn₂, hf₂⟩
  · simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil] at *
    omega

end MinCostFlow.LinkCut.Gen
