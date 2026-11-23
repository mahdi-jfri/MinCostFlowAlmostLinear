module

public import MinCostFlow.LinkCut.Gen.Single

/-!
# `link` as a program

`linkBody` is the machine version of `lctLink`. The free list head of the model lives in one
word at address `fh`, outside the records. The program reroots at `v` and then at `u`, takes the
first free edge slot `ne`, makes it a singleton tree holding the edge value with path parent `u`,
sets the path parent of `v` to `ne`, and pops `ne` from the free list.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-- `lctLink` on `[nb, fh, u, v, va, splayFuel, heap]`, with the edge value in the block at
`va`. -/
def linkBody (rerootProc mkProc noteProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 0))
    (.cond (.bin .eq (.reg 3) (.const 0)) (.ret (.const 0))
      (.cond (.bin .eq (.reg 2) (.reg 3)) (.ret (.const 0))
        (.assign 7 (.load (.reg 1)) ;;
         .cond (.bin .eq (.reg 7) (.const 0)) (.ret (.const 0))
           (.call 8 rerootProc [.reg 0, .reg 3, .reg 5, .reg 6] ;;
            .call 8 rerootProc [.reg 0, .reg 2, .reg 5, .reg 6] ;;
            .assign 9 (.load (.bin .add (recAddr 7) (.const 2))) ;;
            .call 8 mkProc [.reg 0, .reg 7, .reg 4, .reg 2, .reg 6] ;;
            .call 8 noteProc [.reg 0, .reg 7] ;;
            .store (.bin .add (recAddr 3) (.const 3)) (.reg 7) ;;
            .store (.reg 1) (.reg 9) ;;
            .ret (.const 0)))))

theorem linkBody_noRand (a b c : ℕ) :
    (linkBody a b c).NoRand := by
  simp [linkBody, recAddr, Stmt.NoRand]

/-- The state after the two reroots of `lctLink P st u v`. -/
def linkMid (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) : LctState α σ τ :=
  lctReroot P (lctReroot P st v) u

theorem linkMid_freeHead (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) :
    (linkMid P st u v).freeHead = st.freeHead := by
  rw [linkMid, lctReroot_freeHead, lctReroot_freeHead]

theorem lctLink_eq {P : LctPayload α σ τ} {st : LctState α σ τ} {u v : ℕ} {e : α}
    (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) (hf : st.freeHead ≠ 0) :
    lctLink P st u v e =
      { n := st.n,
        splay := (SplayState.makeSingleton P (linkMid P st u v).splay st.freeHead e u).setPpar v
          st.freeHead,
        freeHead := ((linkMid P st u v).splay.nodes st.freeHead).par } := by
  have h2 : (lctRerootCost P (lctRerootCost P st v).1 u).1.freeHead = st.freeHead :=
    linkMid_freeHead P st u v
  unfold lctLink lctLinkCost
  rw [if_neg (by simp [hu, hv, huv, hf])]
  simp only [h2, hf, beq_iff_eq, if_false]
  rfl

/-- The payload values of `lctLink P st u v e` are representable. -/
def LinkOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ)
    (e : α) : Prop :=
  RerootOk ok P st v ∧ RerootOk ok P (lctReroot P st v) u ∧ ok.sumOk (P.single st.freeHead e)

/-- The cost bound of `lctLink P st u v e`. -/
def linkCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) (st : LctState α σ τ) (u v : ℕ) : ℕ :=
  rerootCost S st v + rerootCost S (lctReroot P st v) u + singleCost S + 300

/-- The nodes `lctLink P st u v e` notes: those of the two reroots, then the new edge node. -/
def linkNotes (P : LctPayload α σ τ) (st : LctState α σ τ) (u v : ℕ) (S : List ℕ) :
    List ℕ :=
  if u = 0 ∨ v = 0 ∨ u = v ∨ st.freeHead = 0 then S
  else noteList (exposeNotes P (lctReroot P st v) u (exposeNotes P st v S)) st.freeHead

/-- The frame of a tree operation that may also change the index and the free list word
`fh`. -/
def LinkFrame (Lay : NodeLayout α σ τ) (nb cap fh h : ℕ) (mem mem' : ℕ → ℕ) : Prop :=
  ZeroFrom mem' h ∧
    ∀ a < h, ¬ Lay.InRecords nb cap a → ¬ InIndex nb cap a → a ≠ fh → mem' a = mem a

theorem TreeFrameN.linkFrame {Lay : NodeLayout α σ τ} {nb cap fh h : ℕ} {mem mem' : ℕ → ℕ}
    (hf : TreeFrameN Lay nb cap h mem mem') : LinkFrame Lay nb cap fh h mem mem' :=
  ⟨hf.1, fun a ha hr hi _ => hf.2 a ha hr hi⟩

theorem PtrOk.link {cap u v : ℕ} {P : LctPayload α σ τ} {st : LctState α σ τ} {e : α}
    (h : PtrOk cap st.splay) (hu : u ≤ cap) (hv : v ≤ cap) (hf : st.freeHead ≤ cap) :
    PtrOk cap (lctLink P st u v e).splay := by
  by_cases hc : u ≠ 0 ∧ v ≠ 0 ∧ u ≠ v ∧ st.freeHead ≠ 0
  · rw [lctLink_eq hc.1 hc.2.1 hc.2.2.1 hc.2.2.2]
    exact (((h.reroot hv).reroot hu).makeSingleton hu).setPpar hv hf
  · have : lctLink P st u v e = st := by
      simp only [lctLink, lctLinkCost]
      rw [if_pos]
      simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
      tauto
    rw [this]; exact h

variable {w nb cap heap : ℕ} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
  {ok : PayloadOk α σ τ} {p : Program} {S : PayloadSteps w p P Lay ok}
  {L : LazyProcs w p P Lay ok S} {Q : SplayProcs L} {E : ExposeProcs Q}

/-- The run of `linkBody`. The free list word `fh` and the value block at `va` lie outside the
records and below the heap pointer, and do not overlap. -/
theorem linkBody_runs (hL : P.Laws) (R : PathProcs E) {mk : ℕ}
    (hmk : p.procs[mk]? = some (makeSingletonBody L.copy S.setId Q.pull)) (ω : ℕ → Bool)
    {fh u v va pos : ℕ} {e : α} {mem : ℕ → ℕ} {st : LctState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st.splay) (hfh : mem fh = st.freeHead)
    (hptr : PtrOk cap st.splay) (hu : u ≤ cap) (hv : v ≤ cap) (hfc : st.freeHead ≤ cap)
    (hheap : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem)
    (hfr : ¬ Lay.InRecords nb cap fh) (hfi : ¬ InIndex nb cap fh) (hfh' : fh < heap)
    (hva : Lay.nodeAddr nb (cap + 1) ≤ va) (hvh : va + Lay.valW ≤ heap)
    (hfva : fh < va ∨ va + Lay.valW ≤ fh) (hval : Lay.ValAt mem va e)
    (hn : 2 * st.n + 1 < 2 ^ w) (hok : LinkOk ok P st u v e)
    (hnb : 2 * cap + 3 ≤ nb) {I : List ℕ} (hI : IdxAt mem nb cap I) :
    ∃ o st' c, Runs w p ω (linkBody R.reroot mk E.note)
        (startState [nb, fh, u, v, va, 2 * st.n + 1, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (lctLink P st u v e).splay ∧
        st'.mem fh = (lctLink P st u v e).freeHead ∧ LinkFrame Lay nb cap fh heap mem st'.mem ∧
        IdxAt st'.mem nb cap (linkNotes P st u v I)) ∧
      0 + c ≤ linkCost S st u v := by
  have hnh := hheap.nb_le
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS := hheap.stride_lt
  have hS6 := Lay.stride_pos
  have hrec := hheap.rec_le
  have hlt : ∀ y ≤ cap, nb + Lay.nodeStride * y + Lay.nodeStride ≤ heap := fun y hy => by
    have := hheap.addr_lt hy; unfold nodeAddr at this; exact this
  have hAv := hlt v hv
  have hAf := hlt _ hfc
  have hvS : v ≤ Lay.nodeStride * v := Nat.le_mul_of_pos_left v (by omega)
  have hfS : st.freeHead ≤ Lay.nodeStride * st.freeHead :=
    Nat.le_mul_of_pos_left _ (by omega)
  have huS : u ≤ Lay.nodeStride * u := Nat.le_mul_of_pos_left u (by omega)
  have hAu := hlt u hu
  have hsame : ∀ m : ℕ → ℕ, TreeFrameN Lay nb cap heap mem m → m fh = mem fh :=
    fun m hm => hm.2 fh hfh' hfr hfi
  have hvalm : ∀ m : ℕ → ℕ, TreeFrameN Lay nb cap heap mem m → Lay.ValAt m va e :=
    fun m hm => Lay.val_congr _ _ _ _ hval fun i hi => hm.2 _ (by omega) (fun hr => by
      have := hr.2; unfold nodeAddr at this hva; omega) fun hx => by
      have := hx.2; unfold nodeAddr at hva; omega
  have htriv : ∀ (m : State), m.mem = mem → (u = 0 ∨ v = 0 ∨ u = v ∨ st.freeHead = 0) →
      (Lay.NodesAt m.mem nb cap st.splay ∧ m.mem fh = st.freeHead ∧
        LinkFrame Lay nb cap fh heap mem m.mem ∧ IdxAt m.mem nb cap (linkNotes P st u v I)) :=
    fun m hm hc => by
      rw [hm]
      exact ⟨hnodes, hfh, ⟨hheap.zero, fun _ _ _ _ _ => rfl⟩, by simpa [linkNotes, hc] using hI⟩
  have hstay : ∀ (h : u = 0 ∨ v = 0 ∨ u = v ∨ st.freeHead = 0), lctLink P st u v e = st := by
    intro h
    simp only [lctLink, lctLinkCost]
    rw [if_pos]
    simp only [beq_iff_eq, Bool.or_eq_true, decide_eq_true_eq]
    tauto
  unfold linkBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · rw [hstay (Or.inl hcond)]
    wram_step
    · exact htriv _ rfl (Or.inl hcond)
    · simp only [linkCost]; wram_cost
  have hu0 : u ≠ 0 := hcond
  wram_step
  · rw [hstay (Or.inr (Or.inl hcond))]
    wram_step
    · exact htriv _ rfl (Or.inr (Or.inl hcond))
    · simp only [linkCost]; wram_cost
  have hv0 : v ≠ 0 := hcond
  wram_step
  · rw [hstay (Or.inr (Or.inr (Or.inl hcond)))]
    wram_step
    · exact htriv _ rfl (Or.inr (Or.inr (Or.inl hcond)))
    · simp only [linkCost]; wram_cost
  have huv : u ≠ v := hcond
  wram_step; try dsimp only
  rw [hfh]
  wram_step
  · rw [hstay (Or.inr (Or.inr (Or.inr hcond)))]
    wram_step
    · exact htriv _ rfl (Or.inr (Or.inr (Or.inr hcond)))
    · simp only [linkCost]; wram_cost
  have hf0 : st.freeHead ≠ 0 := hcond
  obtain ⟨ok₁, ok₂, ok₃⟩ := hok
  set ne := st.freeHead with hne
  -- reroot at `v`, then at `u`
  refine runs_seq_callBody_le R.reroot_body (by eval_expr)
    (R := fun _ m₁ c₁ => Lay.NodesAt m₁.mem nb cap (lctReroot P st v).splay ∧
      IdxFrame Lay nb cap heap mem m₁.mem (exposeNotes P st v I) ∧ c₁ ≤ rerootCost S st v) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := rerootBody_runs (E := E) ω (pos := pos) hnodes hptr
      hv hheap hn ok₁ hnb hI
    exact ⟨o, st', c, by simpa using hr, hn', hf, by omega⟩
  rintro - m₁ c₁ ⟨hn₁, hf₁, hc₁⟩
  refine runs_seq_callBody_le R.reroot_body (by eval_expr)
    (R := fun _ m₂ c₂ => Lay.NodesAt m₂.mem nb cap (linkMid P st u v).splay ∧
      IdxFrame Lay nb cap heap mem m₂.mem
        (exposeNotes P (lctReroot P st v) u (exposeNotes P st v I)) ∧
      c₂ ≤ rerootCost S (lctReroot P st v) u) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := rerootBody_runs (E := E) ω (pos := m₁.pos)
      (st := lctReroot P st v) hn₁ (hptr.reroot hv) hu ⟨hrec, hroom, hf₁.1.1, hwide⟩ hn ok₂
      hnb hf₁.2
    exact ⟨o, st', c, by simpa [lctReroot_n] using hr, hn', hf₁.trans hf, by omega⟩
  rintro - m₂ c₂ ⟨hn₂, hf₂, hc₂⟩
  have hp₂ : PtrOk cap (linkMid P st u v).splay := (hptr.reroot hv).reroot hu
  -- the next free slot
  have hm₂ : m₂.mem (nb + Lay.nodeStride * ne + 2) = ((linkMid P st u v).splay.nodes ne).par :=
    (hn₂ ne hfc).2.2.1
  wram_step; try dsimp only
  rw [hm₂]
  -- make `ne` a singleton
  refine runs_seq_callBody_le hmk (by eval_expr)
    (R := fun _ m₃ c₃ => Lay.NodesAt m₃.mem nb cap
        (SplayState.makeSingleton P (linkMid P st u v).splay ne e u) ∧
      IdxFrame Lay nb cap heap mem m₃.mem
        (exposeNotes P (lctReroot P st v) u (exposeNotes P st v I)) ∧ c₃ ≤ singleCost S) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := makeSingletonBody_runs hL S L.copy_ok Q.pull_body ω
      (pos := m₂.pos) hn₂ hp₂ hfc hf0 hu ⟨hrec, by omega, hf₂.1.1, hwide⟩ hva hvh
      (hvalm _ hf₂.1) ok₃
    exact ⟨o, st', c, by simpa using hr, hn', hf₂.trans_tree hnb hnh hf, by omega⟩
  rintro - m₃₀ c₃ ⟨hn₃₀, hf₃₀, hc₃⟩
  refine runs_seq_note (S := exposeNotes P (lctReroot P st v) u (exposeNotes P st v I)) E.note_body
    (by eval_expr) (by eval_expr) hfc hnb hnh (by omega) hn₃₀ hf₃₀ rfl fun v₃ m₃ hn₃ hF₃ => ?_
  have hf₃ := hF₃.1
  -- the path parent of `v`, and the free list
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₄ hM₄ => ?_
  have h₄ : Lay.NodesAt M₄ nb cap
      ((SplayState.makeSingleton P (linkMid P st u v).splay ne e u).setPpar v ne) ∧
      TreeFrame Lay nb cap heap m₃.mem M₄ := by
    rw [hM₄]; exact NodesAt.ctrl hn₃ (TreeFrame.refl hf₃.1) hv (by decide) (hheap.addr_lt hv)
      (fun h => h.setPpar Lay hv)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₅ hM₅ => ?_
  wram_step
  · rw [lctLink_eq hu0 hv0 huv hf0]
    dsimp only
    refine ⟨?_, ?_, ⟨?_, ?_⟩, ?_⟩
    · rw [hM₅]
      exact h₄.1.congr Lay fun a ha => Function.update_of_ne (by rintro rfl; exact hfr ha) _ _
    · rw [hM₅]; simp only [Function.update_self]; rfl
    · intro a ha
      rw [hM₅, Function.update_of_ne (by omega)]; exact h₄.2.1 a ha
    · intro a ha hr hi hafh
      rw [hM₅, Function.update_of_ne hafh]; dsimp only; rw [h₄.2.2 a ha hr]; exact hf₃.2 a ha hr hi
    · have hI₄ := hF₃.2.of_treeFrame hnb hnh h₄.2
      rw [show linkNotes P st u v I = noteList
          (exposeNotes P (lctReroot P st v) u (exposeNotes P st v I)) ne by
        simp only [linkNotes, hu0, hv0, huv, ← hne, hf0, false_or, if_false]]
      refine hI₄.congr hnb fun a ha => ?_
      rw [hM₅, Function.update_of_ne]; rintro rfl; exact hfi ha
  · simp only [linkCost]
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
      argsSize_cons, argsSize_nil] at *
    omega

end MinCostFlow.LinkCut.Gen
