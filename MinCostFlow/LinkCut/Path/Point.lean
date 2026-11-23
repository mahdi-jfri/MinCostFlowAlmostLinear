module

public import MinCostFlow.LinkCut.Gen.Expose
public import MinCostFlow.LinkCut.Path.ReadVal
public import MinCostFlow.LinkCut.Path.WriteVal
public import MinCostFlow.LinkCut.Path.Steps

/-!
# Point read and point write for the path tree

A point read exposes the node, then copies its edge value out, in the interface width `L`, to
the heap pointer. It returns the new heap pointer, just past the copied value.

A point write exposes the node, copies a new edge value in from `L` limbs to `K` limbs, and
recomputes the node's summary with `pull`. Since the node is the root of its tree after the
expose, no other summary depends on it.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen
  MinCostFlow.LinkCut.Gen.NodeLayout

/-- `pointRead [nb, x, F, L, heap]`: expose `x`, then copy its value to `heap`. `K` is read
from the record of node `0`. -/
def pointReadBody (exposeProc readValProc : ℕ) : Stmt :=
  strideLoad ;;
  .call 5 exposeProc [.reg 0, .reg 1, .reg 2, .reg 4] ;;
  .assign 6 (recAddr 1) ;;
  .assign 7 (.load (.bin .add (.reg 0) (.const 9))) ;;
  .call 5 readValProc [.bin .add (.reg 6) (.const 10), .reg 4, .reg 7, .reg 3] ;;
  .ret (.bin .add (.reg 4) (.bin .add (.const 2) (.bin .mul (.const 4) (.reg 3))))

theorem pointReadBody_noRand (a b : ℕ) : (pointReadBody a b).NoRand := by
  simp [pointReadBody, recAddr, Stmt.NoRand]

/-- The run of `pointReadBody`: the records hold the exposed state, only the new value cells
change outside the records, and the value of `x` is at `heap` in `L` limbs. -/
theorem pointReadBody_runs {w h K L nb cap heap x pos rv : ℕ} {p : Program}
    {S : PayloadSteps w p pathPayload (pathLayout h K) (pathOk h K)}
    {Lz : LazyProcs w p pathPayload (pathLayout h K) (pathOk h K) S} {Q : SplayProcs Lz}
    (E : ExposeProcs Q) (hrv : MeetsContract w p rv (readValContract w h K L)) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    (hnodes : (pathLayout h K).NodesAt mem nb cap st.splay) (hptr : PtrOk cap st.splay)
    (hx : x ≤ cap) (hheap : HeapOk (pathLayout h K) w nb cap heap
      (2 * (pathLayout h K).tagW + S.space) mem)
    (hn : 2 * st.n + 1 < 2 ^ w) (hok : ExposeOk (pathOk h K) pathPayload st x)
    (hLK : L ≤ K) (hroomL : heap + (2 + 4 * L) < 2 ^ w)
    (hfit : PathEdgeFits h L ((lctExpose pathPayload st x).splay.nodes x).val)
    (hnb : 2 * cap + 3 ≤ nb) {I : List ℕ} (hI : IdxAt mem nb cap I) :
    ∃ o st' c, Runs w p ω (pointReadBody E.expose rv)
        (startState [nb, x, 2 * st.n + 1, L, heap] mem pos) o st' c ∧
      ((pathLayout h K).NodesAt st'.mem nb cap (lctExpose pathPayload st x).splay ∧
        (∀ y < heap, ¬ (pathLayout h K).InRecords nb cap y → ¬ InIndex nb cap y →
          st'.mem y = mem y) ∧
        IdxAt st'.mem nb cap (exposeNotes pathPayload st x I) ∧
        ZeroFrom st'.mem (heap + (2 + 4 * L)) ∧
        PathEdgeAt st'.mem heap h L ((lctExpose pathPayload st x).splay.nodes x).val ∧
        o.value = heap + (2 + 4 * L)) ∧
      0 + c ≤ exposeCost S st x + 68 * L + 350 := by
  have hroom := hheap.room
  have hrec := hheap.addr_lt hx
  have hSw := hheap.stride_lt
  have hnb9 := hheap.nb9
  rw [pathLayout_stride] at hrec hSw
  unfold pointReadBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  refine runs_seq_callBody_le E.expose_body (by eval_expr)
    (R := fun _ m₁ c₁ => (pathLayout h K).NodesAt m₁.mem nb cap
      (lctExpose pathPayload st x).splay ∧
      IdxFrame (pathLayout h K) nb cap heap mem m₁.mem (exposeNotes pathPayload st x I) ∧
      c₁ ≤ exposeCost S st x) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := exposeBody_runs E ω (pos := pos) hnodes hptr hx
      hheap hn hok hnb hI
    exact ⟨o, st', c, by simpa [startState] using hr, hn', hf, by omega⟩
  rintro - m₁ c₁ ⟨hn₁, ⟨⟨hz₁, hf₁⟩, hI₁⟩, hc₁⟩
  have hnh := hheap.nb_le
  have hA : (pathLayout h K).nodeAddr nb x = nb + (13 + 9 * K) * x := by
    simp only [nodeAddr, pathLayout_stride]
  refine runs_seq_assign_le (v := (pathLayout h K).nodeAddr nb x)
    (eval_recAddr (by simp) (by simp) (by simp) (by rw [hA]; omega)) ?_
  have hK9 : m₁.mem (nb + 9) = K := by
    have := (hn₁ 0 (Nat.zero_le _)).2.2.2.2.2.2.1.2.2.2.1
    simpa [nodeAddr, OFF_VAL] using this
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) hK9) ?_
  have hval : PathEdgeAt m₁.mem ((pathLayout h K).nodeAddr nb x + 6 + 4) h K
      ((lctExpose pathPayload st x).splay.nodes x).val := (hn₁ x hx).2.2.2.2.2.2.1.2.2.2.2
  rw [hA, show nb + (13 + 9 * K) * x + 6 + 4 = nb + (13 + 9 * K) * x + 10 by omega] at hval
  refine runs_seq_call_le hrv (vs := [nb + (13 + 9 * K) * x + 10, heap, K, L])
    (by simp only [hA] at *; eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, rfl, by have := hheap.wide; omega, hLK, by omega, hroomL, Or.inl (by omega), _,
      hval, hfit⟩ ?_
  rintro v₂ m₂ pos₂ ⟨hf₂, hp₂⟩
  simp only [List.getD_cons_zero, List.getD_cons_succ] at hf₂ hp₂
  have hkeep : ∀ y < heap, m₂ y = m₁.mem y := fun y hy => hf₂ y (by omega)
  refine runs_ret_le (by eval_expr) ⟨?_, fun y hy hn hi => ?_, ?_, fun y hy => ?_, ?_, rfl⟩ ?_
  · exact NodesAt.congr (pathLayout h K) hn₁ fun a ha => hkeep a (by
      have := hheap.rec_le; exact lt_of_lt_of_le ha.2 this)
  · exact (hkeep y hy).trans (hf₁ y hy hn hi)
  · exact hI₁.congr hnb fun a ha => hkeep a (by have := ha.2; omega)
  · show m₂ y = 0
    rw [hf₂ y (by omega)]; exact hz₁ y (by omega)
  · exact hp₂ _ hval hfit
  · simp only [readValContract, Expr.size_reg, Expr.size_const, Expr.size_bin, argsSize_cons,
      argsSize_nil, Expr.size_load] at *
    omega

/-- `pointWrite [nb, x, va, F, L, heap]`: expose `x`, write the value at `va` into it, pull.
`K` is read from the record of node `0`. -/
def pointWriteBody (exposeProc writeValProc pullProc : ℕ) : Stmt :=
  strideLoad ;;
  .call 6 exposeProc [.reg 0, .reg 1, .reg 3, .reg 5] ;;
  .assign 7 (recAddr 1) ;;
  .assign 8 (.load (.bin .add (.reg 0) (.const 9))) ;;
  .call 6 writeValProc [.reg 2, .bin .add (.reg 7) (.const 10), .reg 4, .reg 8, .reg 5] ;;
  .call 6 pullProc [.reg 0, .reg 1, .reg 5] ;;
  .ret (.reg 5)

theorem pointWriteBody_noRand (a b c : ℕ) : (pointWriteBody a b c).NoRand := by
  simp [pointWriteBody, recAddr, Stmt.NoRand]

/-- The node state after a point write: `x` exposed, its value replaced, its summary pulled. -/
def pointWriteSplay (st : LctState (Option PathEdgeValue) PathSummary PathTag) (x : ℕ)
    (v : Option PathEdgeValue) : SplayState (Option PathEdgeValue) PathSummary PathTag :=
  SplayState.pull pathPayload
    ((lctExpose pathPayload st x).splay.updateNode x fun nd => { nd with val := v }) x

/-- The run of `pointWriteBody`. The new value lies outside the records, below the heap. -/
theorem pointWriteBody_runs {w h K L nb cap heap x va pos wv : ℕ} {p : Program}
    {S : PayloadSteps w p pathPayload (pathLayout h K) (pathOk h K)}
    {Lz : LazyProcs w p pathPayload (pathLayout h K) (pathOk h K) S} {Q : SplayProcs Lz}
    (E : ExposeProcs Q) (hwv : MeetsContract w p wv (writeValContract w h L K)) (ω : ℕ → Bool)
    {mem : ℕ → ℕ} {st : LctState (Option PathEdgeValue) PathSummary PathTag}
    {e : PathEdgeValue}
    (hnodes : (pathLayout h K).NodesAt mem nb cap st.splay) (hptr : PtrOk cap st.splay)
    (hx : x ≤ cap) (hheap : HeapOk (pathLayout h K) w nb cap heap
      (2 * (pathLayout h K).tagW + S.space) mem)
    (hn : 2 * st.n + 1 < 2 ^ w) (hok : ExposeOk (pathOk h K) pathPayload st x)
    (hLK : L ≤ K) (hva : (pathLayout h K).nodeAddr nb (cap + 1) ≤ va)
    (hvah : va + (2 + 4 * L) ≤ heap) (hval : PathEdgeAt mem va h L (some e))
    (hokp : x ≠ 0 → (pathOk h K).sumOk (pullSum pathPayload
      ((lctExpose pathPayload st x).splay.updateNode x fun nd => { nd with val := some e }) x))
    (hnb : 2 * cap + 3 ≤ nb) {I : List ℕ} (hI : IdxAt mem nb cap I) :
    ∃ o st' c, Runs w p ω (pointWriteBody E.expose wv Q.pull)
        (startState [nb, x, va, 2 * st.n + 1, L, heap] mem pos) o st' c ∧
      ((pathLayout h K).NodesAt st'.mem nb cap (pointWriteSplay st x (some e)) ∧
        IdxFrame (pathLayout h K) nb cap heap mem st'.mem (exposeNotes pathPayload st x I) ∧
        o.value = heap) ∧
      0 + c ≤ exposeCost S st x + (300 * K + 600) + S.cost + 400 := by
  have hroom := hheap.room
  have hrec := hheap.addr_lt hx
  have hSw := hheap.stride_lt
  have hwide := hheap.wide
  have hrl := hheap.rec_le
  rw [pathLayout_stride] at hrec hSw
  have htagW : (pathLayout h K).tagW = 2 * K := rfl
  have hnb9 := hheap.nb9
  rw [htagW] at hroom
  unfold pointWriteBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  refine runs_seq_callBody_le E.expose_body (by eval_expr)
    (R := fun _ m₁ c₁ => (pathLayout h K).NodesAt m₁.mem nb cap
      (lctExpose pathPayload st x).splay ∧
      IdxFrame (pathLayout h K) nb cap heap mem m₁.mem (exposeNotes pathPayload st x I) ∧
      c₁ ≤ exposeCost S st x) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := exposeBody_runs E ω (pos := pos) hnodes hptr hx
      hheap hn hok hnb hI
    exact ⟨o, st', c, by simpa [startState] using hr, hn', hf, by omega⟩
  rintro - m₁ c₁ ⟨hn₁, ⟨⟨hz₁, hf₁⟩, hI₁⟩, hc₁⟩
  have hnh := hheap.nb_le
  have hA : (pathLayout h K).nodeAddr nb x = nb + (13 + 9 * K) * x := by
    simp only [nodeAddr, pathLayout_stride]
  refine runs_seq_assign_le (v := (pathLayout h K).nodeAddr nb x)
    (eval_recAddr (by simp) (by simp) (by simp) (by rw [hA]; omega)) ?_
  have hK9 : m₁.mem (nb + 9) = K := by
    have := (hn₁ 0 (Nat.zero_le _)).2.2.2.2.2.2.1.2.2.2.1
    simpa [nodeAddr, OFF_VAL] using this
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) hK9) ?_
  have hnotrec : ∀ i < 2 + 4 * L, ¬ (pathLayout h K).InRecords nb cap (va + i) := fun i hi hc =>
    by have := hc.2; omega
  have hmulx : (13 + 9 * K) * x + (13 + 9 * K) ≤ (13 + 9 * K) * (cap + 1) := by
    rw [Nat.mul_succ]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hx) _
  have hvanb : nb ≤ va := by unfold nodeAddr at hva; omega
  have hval₁ : PathEdgeAt m₁.mem va h L (some e) :=
    pathEdgeAt_move hval fun i hi => hf₁ _ (by omega) (hnotrec i (by omega)) fun hi' => by
      have := hi'.2; omega
  have hcapA : (pathLayout h K).nodeAddr nb (cap + 1) = nb + (13 + 9 * K) * (cap + 1) := by
    simp only [nodeAddr, pathLayout_stride]
  rw [hcapA] at hrl hva
  refine runs_seq_call_le hwv (vs := [va, nb + (13 + 9 * K) * x + 10, L, K, heap])
    (by simp only [hA] at *; eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨⟨_, _, _, rfl, by omega, hLK, hvah, by omega, Or.inr (by
      have hmul : (13 + 9 * K) * x + (13 + 9 * K) ≤ (13 + 9 * K) * (cap + 1) := by
        rw [Nat.mul_succ]; exact Nat.add_le_add_right (Nat.mul_le_mul_left _ hx) _
      omega), _, hval₁⟩, hz₁, show heap + 2 * K < 2 ^ w by omega⟩ ?_
  rintro v₂ m₂ pos₂ ⟨hz₂, hf₂, hp₂⟩
  change ZeroFrom m₂ heap at hz₂
  change ∀ y < heap, ¬ (nb + (13 + 9 * K) * x + 10 ≤ y ∧
    y < nb + (13 + 9 * K) * x + 10 + (2 + 4 * K)) → m₂ y = m₁.mem y at hf₂
  have hv₂ : PathEdgeAt m₂ (nb + (13 + 9 * K) * x + 10) h K (some e) := hp₂ e hval₁
  set ex := (lctExpose pathPayload st x).splay with hex
  have hn₂ : (pathLayout h K).NodesAt m₂ nb cap
      (ex.updateNode x fun nd => { nd with val := some e }) := by
    have hpay := NodesAt.payload (v := some e) (s := (ex.nodes x).sum) (t := (ex.nodes x).tag)
      hn₁ hx hz₁ hz₂ (fun y hy hn => hf₂ y hy fun hc => hn (by
        unfold PayCell; rw [hA, pathLayout_stride]; unfold OFF_VAL; omega))
      (by
        have h0 := (hn₁ x hx).2.2.2.2.2.2.1
        change PathValAt m₁.mem ((pathLayout h K).nodeAddr nb x + 6) h K _ at h0
        show PathValAt m₂ ((pathLayout h K).nodeAddr nb x + 6) h K (some e)
        rw [hA] at h0 ⊢
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · rw [hf₂ _ (by omega) (by omega)]; exact h0.1
        · rw [hf₂ _ (by omega) (by omega)]; exact h0.2.1
        · rw [hf₂ _ (by omega) (by omega)]; exact h0.2.2.1
        · rw [hf₂ _ (by omega) (by omega)]; exact h0.2.2.2.1
        · rw [show nb + (13 + 9 * K) * x + 6 + 4 = nb + (13 + 9 * K) * x + 10 by omega]
          exact hv₂)
      (by
        have := (hn₁ x hx).2.2.2.2.2.2.2.1
        rw [pathLayout_offSum] at this ⊢
        rw [hA] at this ⊢
        exact pathSummaryAt_move this fun i hi => hf₂ _ (by omega) (by omega))
      (by
        have := (hn₁ x hx).2.2.2.2.2.2.2.2
        rw [pathLayout_offTag] at this ⊢
        rw [hA] at this ⊢
        exact pathTagAt_move this fun i hi => hf₂ _ (by omega) (by omega))
    exact hpay
  have hptr₂ : PtrOk cap (ex.updateNode x fun nd => { nd with val := some e }) :=
    (hptr.expose hx).updateNode_ptrs ((hptr.expose hx) x hx)
  have hheap₂ : HeapOk (pathLayout h K) w nb cap heap S.space m₂ :=
    ⟨hheap.rec_le, by have := hheap.room; omega, hz₂, hwide⟩
  refine runs_seq_callBody_le Q.pull_body (by eval_expr)
    (R := fun _ m₃ c₃ => (pathLayout h K).NodesAt m₃.mem nb cap (pointWriteSplay st x (some e)) ∧
      TreeFrame (pathLayout h K) nb cap heap m₂ m₃.mem ∧ c₃ ≤ S.cost + 150) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn', hf⟩, hc⟩ := pullBody_runs S ω (pos := pos₂) hn₂ hptr₂ hx
      hheap₂ hokp
    exact ⟨o, st', c, by simpa [startState] using hr, hn', hf, by omega⟩
  rintro - m₃ c₃ ⟨hn₃, ⟨hz₃, hf₃⟩, hc₃⟩
  refine runs_ret_le (by eval_expr) ⟨hn₃, ⟨⟨hz₃, fun y hy hr hi => ?_⟩, ?_⟩, rfl⟩ ?_
  · rw [hf₃ y hy hr, hf₂ y hy fun hc => hr ?_, hf₁ y hy hr hi]
    show nb ≤ y ∧ y < (pathLayout h K).nodeAddr nb (cap + 1)
    rw [hcapA]
    exact ⟨by omega, by omega⟩
  · refine hI₁.congr hnb fun a ha => ?_
    have ha2 := ha.2
    rw [hf₃ a (by omega) (not_inRecords_of_inIndex ha), hf₂ a (by omega) (by omega)]
  · simp only [writeValContract, payloadContract, Expr.size_reg, Expr.size_const,
      Expr.size_bin, argsSize_cons, argsSize_nil, Expr.size_load] at *
    omega

end MinCostFlow.LinkCut.Path
