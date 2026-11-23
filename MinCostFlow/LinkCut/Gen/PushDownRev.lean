module

public import MinCostFlow.LinkCut.Gen.ApplyTag

/-!
# `pushDownRev` as a program

`pushDownRevBody` is the machine version of `SplayState.pushDownRev`: if node `x ≠ 0` has its
reversal bit set, it clears the bit and calls `revNode` (procedure `revProc`, with body
`revNodeBody`) on the left and then on the right child of `x`, both read before the first call.
The arguments are `[nb, x, heap]`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-- `pushDownRev` on `[nb, x, heap]`. -/
def pushDownRevBody (revProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 3 (recAddr 1) ;;
     .cond (.load (.bin .add (.reg 3) (.const 5)))
       (.assign 4 (.load (.reg 3)) ;;
        .assign 5 (.load (.bin .add (.reg 3) (.const 1))) ;;
        .store (.bin .add (.reg 3) (.const 5)) (.const 0) ;;
        .call 6 revProc [.reg 0, .reg 4, .reg 2] ;;
        .call 6 revProc [.reg 0, .reg 5, .reg 2] ;;
        .ret (.const 0))
       (.ret (.const 0)))

theorem pushDownRevBody_noRand (revProc : ℕ) :
    (pushDownRevBody revProc).NoRand := by
  simp [pushDownRevBody, recAddr, Stmt.NoRand]

/-- Reversing the node `nd` gives representable payload values. -/
def RevOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (nd : SplayNode α σ τ) : Prop :=
  ok.valOk (P.revVal nd.val) ∧ ok.sumOk (P.revSum nd.sum) ∧ ok.tagOk (P.revTag nd.tag)

/-- The payload values that `pushDownRev P st x` computes are representable. -/
def PushDownRevOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : SplayState α σ τ)
    (x : ℕ) : Prop :=
  x ≠ 0 → (st.nodes x).rev = true →
    let st₀ := st.updateNode x fun cur => { cur with rev := false }
    ((st.nodes x).left ≠ 0 → RevOk ok P (st₀.nodes (st.nodes x).left)) ∧
    ((st.nodes x).right ≠ 0 →
      RevOk ok P ((SplayState.revNode P st₀ (st.nodes x).left).nodes (st.nodes x).right))

/-- The run of `pushDownRevBody`. -/
theorem pushDownRevBody_runs {w nb cap x heap pos revProc : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (hrev : p.procs[revProc]? = some (revNodeBody S.rev))
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap S.space mem) (hok : PushDownRevOk ok P st x) :
    ∃ o st' c, Runs w p ω (pushDownRevBody revProc) (startState [nb, x, heap] mem pos) o st'
        c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.pushDownRev P st x) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧ 0 + c ≤ 2 * S.cost + 200 := by
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS := hheap.stride_lt
  have hS6 := Lay.stride_pos
  have hA := hheap.addr_lt hx
  have hxS : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
  obtain ⟨hpl, hpr, -, -⟩ := hptr x hx
  obtain ⟨h0, h1, -, -, -, h5, -, -, -⟩ := hnodes x hx
  have hm0 : mem (nb + Lay.nodeStride * x) = (st.nodes x).left := h0
  have hm1 : mem (nb + Lay.nodeStride * x + 1) = (st.nodes x).right := h1
  have hm5 : mem (nb + Lay.nodeStride * x + 5) = if (st.nodes x).rev then 1 else 0 := h5
  have hlw : (st.nodes x).left < 2 ^ w := by
    have := hheap.addr_lt hpl; unfold nodeAddr at this
    have : (st.nodes x).left ≤ Lay.nodeStride * (st.nodes x).left :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hrw : (st.nodes x).right < 2 ^ w := by
    have := hheap.addr_lt hpr; unfold nodeAddr at this
    have : (st.nodes x).right ≤ Lay.nodeStride * (st.nodes x).right :=
      Nat.le_mul_of_pos_left _ (by omega)
    omega
  have hAx := hA
  unfold nodeAddr at hA
  unfold pushDownRevBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [SplayState.pushDownRev] using hnodes, TreeFrame.refl hheap.zero⟩
    · wram_cost
  · wram_step; try dsimp only
    have hrevw : (if (st.nodes x).rev then 1 else 0) < 2 ^ w := by split_ifs <;> omega
    refine runs_cond_le (Expr.eval_load_of_eq (by eval_expr) (by simpa using hm5)) ?_ ?_
    · intro hrv
      have hrv' : (st.nodes x).rev = true := by by_contra h; simp [h] at hrv
      obtain ⟨okl, okr⟩ := hok hcond hrv'
      wram_step; try dsimp only; rw [hm0]
      wram_step; try dsimp only; rw [hm1]
      wram_step; try dsimp only
      -- the records after clearing the bit
      set st₀ := st.updateNode x fun cur => { cur with rev := false } with hst₀
      have hn₀ := hnodes.clearRev Lay hx
      have hz₀ : ZeroFrom (Function.update mem (Lay.nodeAddr nb x + NodeLayout.OFF_REV) 0) heap :=
        fun a ha => by rw [Function.update_of_ne (by unfold nodeAddr NodeLayout.OFF_REV; omega)];
                       exact hheap.zero a ha
      have hptr₀ : PtrOk cap st₀ := fun y hy => by
        by_cases hyx : y = x
        · subst hyx; simpa [st₀] using hptr y hy
        · simpa [st₀, hyx] using hptr y hy
      have hh₀ : HeapOk Lay w nb cap heap S.space
          (Function.update mem (Lay.nodeAddr nb x + NodeLayout.OFF_REV) 0) :=
        ⟨hheap.rec_le, hroom, hz₀, hwide⟩
      have hfr₀ : TreeFrame Lay nb cap heap mem
          (Function.update mem (Lay.nodeAddr nb x + NodeLayout.OFF_REV) 0) :=
        TreeFrame.of_ctrl hx (by decide) hAx hheap.zero
      refine runs_seq_callBody_le hrev (by eval_expr)
        (R := fun _ st₁ c₁ => Lay.NodesAt st₁.mem nb cap
          (SplayState.revNode P st₀ (st.nodes x).left) ∧
          TreeFrame Lay nb cap heap mem st₁.mem ∧ c₁ ≤ S.cost + 70) ?_ ?_
      · obtain ⟨v, st', c, hr, hn, hf, hc⟩ := revNodeBody_runs S ω hn₀ hpl hh₀ okl
        exact ⟨.returned v, st', c, hr, hn, hfr₀.trans hf, hc⟩
      rintro - st₁ c₁ ⟨hn₁, hf₁, hc₁⟩
      have hh₁ : HeapOk Lay w nb cap heap S.space st₁.mem :=
        ⟨hheap.rec_le, hroom, hf₁.1, hwide⟩
      refine runs_seq_callBody_le hrev (by eval_expr)
        (R := fun _ st₂ c₂ => Lay.NodesAt st₂.mem nb cap (SplayState.revNode P
          (SplayState.revNode P st₀ (st.nodes x).left) (st.nodes x).right) ∧
          TreeFrame Lay nb cap heap mem st₂.mem ∧ c₂ ≤ S.cost + 70) ?_ ?_
      · obtain ⟨v, st', c, hr, hn, hf, hc⟩ := revNodeBody_runs S ω hn₁ hpr hh₁ okr
        exact ⟨.returned v, st', c, hr, hn, hf₁.trans hf, hc⟩
      rintro - st₂ c₂ ⟨hn₂, hf₂, hc₂⟩
      wram_step
      · refine ⟨?_, hf₂⟩
        simpa [SplayState.pushDownRev, hcond, hrv'] using hn₂
      · wram_cost
    · intro hrv
      have hrv' : (st.nodes x).rev = false := by by_contra h; simp_all
      wram_step
      · exact ⟨by simpa [SplayState.pushDownRev, hcond, hrv'] using hnodes,
          TreeFrame.refl hheap.zero⟩
      · wram_cost

end MinCostFlow.LinkCut.Gen
