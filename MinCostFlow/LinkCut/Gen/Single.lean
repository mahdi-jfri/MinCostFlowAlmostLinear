module

public import MinCostFlow.LinkCut.Gen.Reroot

/-!
# `makeSingleton` as a program

`makeSingletonBody` is the machine version of `SplayState.makeSingleton`: it clears the pointers
of the record of `x`, sets its path parent, its size `1` and its reversal bit `0`, copies the
value from a block outside the records, writes the identity tag, and calls `pull`. The model
writes the summary `single x v` directly. The program computes it with `pull`, which gives
`combine empty (combine (single x v) empty)`; the two agree by the payload laws.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout MinCostFlow.LinkCut

variable {α σ τ : Type*}

/-- `makeSingleton` on `[nb, x, va, pp, heap]`, with the value in the block at `va`. -/
def makeSingletonBody (copyProc setIdProc pullProc : ℕ) : Stmt :=
  strideLoad ;;
  .assign 21 (.load (.bin .add (.reg 0) (.const 7))) ;;
  .assign 5 (recAddr 1) ;;
  .store (.reg 5) (.const 0) ;;
  .store (.bin .add (.reg 5) (.const 1)) (.const 0) ;;
  .store (.bin .add (.reg 5) (.const 2)) (.const 0) ;;
  .store (.bin .add (.reg 5) (.const 3)) (.reg 3) ;;
  .store (.bin .add (.reg 5) (.const 4)) (.const 1) ;;
  .store (.bin .add (.reg 5) (.const 5)) (.const 0) ;;
  .call 6 copyProc [.reg 2, .bin .add (.reg 5) (.const 6), .reg 21] ;;
  .call 6 setIdProc [.reg 5, .reg 4] ;;
  .call 6 pullProc [.reg 0, .reg 1, .reg 4] ;;
  .ret (.const 0)

theorem makeSingletonBody_noRand (a b c : ℕ) :
    (makeSingletonBody a b c).NoRand := by
  simp [makeSingletonBody, recAddr, Stmt.NoRand]

/-- Replace the payload of node `x`. -/
def payUpd (st : SplayState α σ τ) (x : ℕ) (v : α) (s : σ) (t : τ) : SplayState α σ τ :=
  st.updateNode x fun nd => { nd with val := v, sum := s, tag := t }

/-- The pointer writes of `makeSingletonBody`, before the payload calls. -/
def singleCtrl (st : SplayState α σ τ) (x pp : ℕ) : SplayState α σ τ :=
  ((((((st.setLeft x 0).setRight x 0).setPar x 0).setPpar x pp).updateNode x
    fun nd => { nd with sz := 1 }).updateNode x fun nd => { nd with rev := false })

theorem PtrOk.makeSingleton {cap x pp : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    {v : α} (h : PtrOk cap st) (hpp : pp ≤ cap) :
    PtrOk cap (SplayState.makeSingleton P st x v pp) := by
  unfold SplayState.makeSingleton SplayState.setNode
  exact h.updateNode_ptrs (by simp [hpp])

/-- The cost bound of one `makeSingleton` call. -/
def singleCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) : ℕ :=
  2 * S.cost + 17 * Lay.valW + 300

/-- The run of `makeSingletonBody`. The value block at `va` lies after the records and below
the heap pointer. -/
theorem makeSingletonBody_runs {w nb cap x va pp heap pos copyProc pullProc : ℕ}
    {P : LctPayload α σ τ} (hL : P.Laws) {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ}
    {p : Program} (S : PayloadSteps w p P Lay ok)
    (hcopy : MeetsContract w p copyProc (copyWordsContract w))
    (hpull : p.procs[pullProc]? = some (pullBody S.pull))
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ} {v : α}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap) (hx0 : x ≠ 0)
    (hpp : pp ≤ cap) (hheap : HeapOk Lay w nb cap heap S.space mem)
    (hva : Lay.nodeAddr nb (cap + 1) ≤ va) (hvh : va + Lay.valW ≤ heap)
    (hval : Lay.ValAt mem va v) (hok : ok.sumOk (P.single x v)) :
    ∃ o st' c, Runs w p ω (makeSingletonBody copyProc S.setId pullProc)
        (startState [nb, x, va, pp, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.makeSingleton P st x v pp) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧ 0 + c ≤ singleCost S := by
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS := hheap.stride_lt
  have hS6 := Lay.stride_pos
  have hrec := hheap.rec_le
  have hA := hheap.addr_lt hx
  have hxS : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
  have hxrec : Lay.nodeAddr nb x + Lay.nodeStride ≤ Lay.nodeAddr nb (cap + 1) := by
    unfold nodeAddr
    have : Lay.nodeStride * x + Lay.nodeStride ≤ Lay.nodeStride * (cap + 1) := by
      rw [← Nat.mul_succ]; exact Nat.mul_le_mul_left _ (by omega)
    omega
  have hstr : Lay.nodeStride = 6 + Lay.valW + Lay.sumW + Lay.tagW := rfl
  have hAx := hA
  unfold nodeAddr at hA hxrec hva
  have hnb9 := hheap.nb9
  unfold makeSingletonBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  refine runs_seq_load0_le (by simp) hnodes.valW (by omega) ?_
  wram_step; try dsimp only
  -- the six control words
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₁ hM₁ => ?_
  have h₁ : Lay.NodesAt M₁ nb cap (st.setLeft x 0) ∧ TreeFrame Lay nb cap heap mem M₁ := by
    rw [hM₁]; exact NodesAt.ctrl (off := 0) hnodes (TreeFrame.refl hheap.zero) hx (by decide) hAx
      (fun h => h.setLeft Lay hx)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₂ hM₂ => ?_
  have h₂ : Lay.NodesAt M₂ nb cap ((st.setLeft x 0).setRight x 0) ∧
      TreeFrame Lay nb cap heap mem M₂ := by
    rw [hM₂]; exact NodesAt.ctrl h₁.1 h₁.2 hx (by decide) hAx (fun h => h.setRight Lay hx)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₃ hM₃ => ?_
  have h₃ : Lay.NodesAt M₃ nb cap (((st.setLeft x 0).setRight x 0).setPar x 0) ∧
      TreeFrame Lay nb cap heap mem M₃ := by
    rw [hM₃]; exact NodesAt.ctrl h₂.1 h₂.2 hx (by decide) hAx (fun h => h.setPar Lay hx)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₄ hM₄ => ?_
  have h₄ : Lay.NodesAt M₄ nb cap ((((st.setLeft x 0).setRight x 0).setPar x 0).setPpar x pp) ∧
      TreeFrame Lay nb cap heap mem M₄ := by
    rw [hM₄]; exact NodesAt.ctrl h₃.1 h₃.2 hx (by decide) hAx (fun h => h.setPpar Lay hx)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₅ hM₅ => ?_
  have h₅ : Lay.NodesAt M₅ nb cap (SplayState.updateNode
      ((((st.setLeft x 0).setRight x 0).setPar x 0).setPpar x pp) x
      fun nd => { nd with sz := 1 }) ∧ TreeFrame Lay nb cap heap mem M₅ := by
    rw [hM₅]; exact NodesAt.ctrl h₄.1 h₄.2 hx (by decide) hAx (fun h => h.setSz Lay hx (sz := 1))
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₆ hM₆ => ?_
  have h₆ : Lay.NodesAt M₆ nb cap (singleCtrl st x pp) ∧ TreeFrame Lay nb cap heap mem M₆ := by
    rw [hM₆]; exact NodesAt.ctrl h₅.1 h₅.2 hx (by decide) hAx (fun h => h.clearRev Lay hx)
  have hval₆ : Lay.ValAt M₆ va v := Lay.val_congr _ _ _ _ hval fun i hi =>
    h₆.2.2 _ (by omega) fun hr => by have := hr.2; unfold nodeAddr at this; omega
  -- copy the value
  have hcopy' := hcopy
  wram_step
  · exact ⟨_, _, _, rfl, by omega, by omega, by omega, Or.inl (by omega)⟩
  rintro - m₇ - ⟨src, dst, len, heq, -, hcp, hout⟩
  simp only [List.cons.injEq, and_true] at heq
  obtain ⟨rfl, rfl, rfl⟩ := heq
  set s₆ := singleCtrl st x pp with hs₆
  obtain ⟨-, -, -, -, -, -, -, hs₆x, ht₆x⟩ := h₆.1 x hx
  have hin : ∀ a, ¬ (a < nb + Lay.nodeStride * x + 6 ∨
      nb + Lay.nodeStride * x + 6 + Lay.valW ≤ a) → Lay.PayCell (Lay.nodeAddr nb x) a := by
    intro a ha
    unfold PayCell nodeAddr OFF_VAL
    omega
  have hz₇ : ZeroFrom m₇ heap := fun a ha => by
    rw [hout a (Or.inr (by omega))]; exact h₆.2.1 a ha
  have hn₇ : Lay.NodesAt m₇ nb cap (payUpd s₆ x v (s₆.nodes x).sum (s₆.nodes x).tag) :=
    NodesAt.payload (v := v) h₆.1 hx h₆.2.1 hz₇
    (fun y _ hy => hout y (by by_contra hc; exact hy (hin y hc)))
    (Lay.val_move _ _ _ _ _ hval₆ fun i hi => hcp i hi)
    (Lay.sum_congr _ _ _ _ hs₆x fun i hi => hout _ (Or.inr (by unfold nodeAddr offSum; omega)))
    (Lay.tag_congr _ _ _ _ ht₆x fun i hi => hout _ (Or.inr (by unfold nodeAddr offTag; omega)))
  have hf₇ : TreeFrame Lay nb cap heap mem m₇ := h₆.2.trans ⟨hz₇, fun a _ hr => hout a (by
    by_contra hc
    exact hr ⟨by omega, by unfold nodeAddr; omega⟩)⟩
  set s₇ := payUpd s₆ x v (s₆.nodes x).sum (s₆.nodes x).tag with hs₇
  -- write the identity tag
  have hsetid := S.setId_ok
  wram_step
  · exact ⟨⟨_, _, rfl, by omega, _, (hn₇ x hx).2.2.2.2.2.2.1⟩, by simpa [heapArg] using hz₇,
      by simp [heapArg]; omega⟩
  rintro - m₈ - ⟨hz₈, hfr₈, hval₈, hsum₈, htag₈⟩
  simp only [heapArg, List.getD_cons_zero] at hz₈ hfr₈ hval₈ hsum₈ htag₈
  obtain ⟨-, -, -, -, -, -, hv₇x, hs₇x, -⟩ := hn₇ x hx
  have hn₈ : Lay.NodesAt m₈ nb cap (payUpd s₇ x (s₇.nodes x).val (s₇.nodes x).sum P.idTag) :=
    NodesAt.payload hn₇ hx hz₇ hz₈ hfr₈ (hval₈ _ hv₇x) (hsum₈ _ hs₇x) htag₈
  have hf₈ : TreeFrame Lay nb cap heap mem m₈ := hf₇.trans ⟨hz₈, fun a ha hr => hfr₈ a ha
    fun hc => hr (by
      unfold PayCell at hc
      simp only [nodeAddr, InRecords] at hc ⊢
      omega)⟩
  set s₈ := payUpd s₇ x (s₇.nodes x).val (s₇.nodes x).sum P.idTag with hs₈
  have hx8 : (s₈.nodes x).left = 0 ∧ (s₈.nodes x).right = 0 ∧ (s₈.nodes x).val = v := by
    simp [s₈, s₇, s₆, payUpd, singleCtrl, SplayState.setLeft, SplayState.setRight, SplayState.setPar,
      SplayState.setPpar]
  have hp₈ : PtrOk cap s₈ := fun y hy => by
    by_cases hyx : y = x
    · subst hyx
      simp [s₈, s₇, s₆, payUpd, singleCtrl, SplayState.setLeft, SplayState.setRight,
        SplayState.setPar, SplayState.setPpar, hpp]
    · simpa [s₈, s₇, s₆, payUpd, singleCtrl, SplayState.setLeft, SplayState.setRight,
        SplayState.setPar, SplayState.setPpar, SplayState.updateNode, hyx] using hptr y hy
  have hsum : pullSum P s₈ x = P.single x v := by
    simp only [pullSum, hx8, if_true]
    rw [hL.combine_empty_left, hL.combine_empty_right]
  -- pull
  refine runs_seq_callBody_le hpull (by eval_expr)
    (R := fun _ m₉ c₉ => Lay.NodesAt m₉.mem nb cap (SplayState.makeSingleton P st x v pp) ∧
      TreeFrame Lay nb cap heap mem m₉.mem ∧ c₉ ≤ S.cost + 150) ?_ ?_
  · obtain ⟨o, st', c, hrun, ⟨hn, hf⟩, hc⟩ := pullBody_runs S ω hn₈ hp₈ hx
      ⟨hheap.rec_le, hroom, hz₈, hwide⟩ (fun _ => by rw [hsum]; exact hok)
    refine ⟨o, st', c, hrun, ?_, hf₈.trans hf, by omega⟩
    have hfin : SplayState.pull P s₈ x = SplayState.makeSingleton P st x v pp := by
      refine splayState_ext fun y => ?_
      rw [SplayState.pull, if_neg hx0]
      by_cases hy : y = x
      · subst hy
        have hs := hsum
        simp only [pullSum] at hs
        simp only [SplayState.makeSingleton, SplayState.setNode, SplayState.nodes_updateNode_self,
          hx8, if_true, hs]
        simp [s₈, s₇, s₆, payUpd, singleCtrl, SplayState.setLeft, SplayState.setRight,
          SplayState.setPar, SplayState.setPpar, hL.combine_empty_left, hL.combine_empty_right]
      · simp [SplayState.makeSingleton, SplayState.setNode, SplayState.updateNode, hy, s₈, s₇,
          s₆, payUpd, singleCtrl, SplayState.setLeft, SplayState.setRight, SplayState.setPar,
          SplayState.setPpar]
    rw [← hfin]; exact hn
  rintro - m₉ c₉ ⟨hn₉, hf₉, hc₉⟩
  wram_step
  · exact ⟨hn₉, hf₉⟩
  · simp only [singleCost, copyWordsContract, setIdContract, payloadContract]; wram_cost

end MinCostFlow.LinkCut.Gen
