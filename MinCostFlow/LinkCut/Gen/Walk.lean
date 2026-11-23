module

public import MinCostFlow.LinkCut.Gen.Splice

/-!
# `leftmostWalk` and `findLeftmost` as programs

`leftmostWalkBody` is the machine version of `SplayState.leftmostWalk`: it walks down left
children, calling `pushDown` on each node first, and returns the last node. It is recursive,
with the fuel as an argument, like the model. `walkSteps` counts the nodes the model visits, and
the cost is at most `walkSteps + 1` times the cost of one visit. `findLeftmostBody` runs the walk
and then splays the node it returns, as `SplayState.findLeftmost`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-- The number of nodes `SplayState.leftmostWalk P st fuel x` visits. -/
def walkSteps (P : LctPayload α σ τ) (st : SplayState α σ τ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x =>
      if x = 0 then 0
      else if ((SplayState.pushDown P st x).nodes x).left = 0 then 1
      else 1 + walkSteps P (SplayState.pushDown P st x) k ((SplayState.pushDown P st x).nodes x).left

/-- The payload values that `leftmostWalk P st fuel x` computes are representable. -/
def WalkOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) : SplayState α σ τ → ℕ → ℕ → Prop
  | _, 0, _ => True
  | st, k + 1, x => x ≠ 0 → PushDownOk ok P st x ∧
      WalkOk ok P (SplayState.pushDown P st x) k ((SplayState.pushDown P st x).nodes x).left

theorem leftmostWalk_ptr {cap : ℕ} {P : LctPayload α σ τ} :
    ∀ (k x : ℕ) {st : SplayState α σ τ}, PtrOk cap st → x ≤ cap →
      PtrOk cap (SplayState.leftmostWalk P st k x).1 ∧ (SplayState.leftmostWalk P st k x).2 ≤ cap
  | 0, x, _, h, hx => ⟨h, hx⟩
  | k + 1, x, st, h, hx => by
    unfold SplayState.leftmostWalk
    dsimp only
    split_ifs with h0 hl
    · exact ⟨h, Nat.zero_le _⟩
    · exact ⟨h.pushDown hx, hx⟩
    · exact leftmostWalk_ptr k _ (h.pushDown hx) ((h.pushDown hx) x hx).1

/-- `leftmostWalk` on `[nb, x, fuel, heap]`; returns the last node. `selfProc` is this
procedure. -/
def leftmostWalkBody (selfProc pdProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 1))
    (.cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
      (.call 4 pdProc [.reg 0, .reg 1, .reg 3] ;;
       .assign 5 (.load (recAddr 1)) ;;
       .cond (.bin .eq (.reg 5) (.const 0)) (.ret (.reg 1))
         (.call 6 selfProc [.reg 0, .reg 5, .bin .sub (.reg 2) (.const 1), .reg 3] ;;
          .ret (.reg 6))))

theorem leftmostWalkBody_noRand (selfProc pdProc : ℕ) :
    (leftmostWalkBody selfProc pdProc).NoRand := by
  simp [leftmostWalkBody, recAddr, Stmt.NoRand]

/-- The run of `leftmostWalkBody`. -/
theorem leftmostWalkBody_runs {w nb cap heap wp : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    {S : PayloadSteps w p P Lay ok} (L : LazyProcs w p P Lay ok S)
    (hself : p.procs[wp]? = some (leftmostWalkBody wp L.pushDown)) (ω : ℕ → Bool) :
    ∀ (k x pos : ℕ) {mem : ℕ → ℕ} {st : SplayState α σ τ},
    Lay.NodesAt mem nb cap st → PtrOk cap st → x ≤ cap →
    HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem → k < 2 ^ w → WalkOk ok P st k x →
    ∃ o st' c, Runs w p ω (leftmostWalkBody wp L.pushDown)
        (startState [nb, x, k, heap] mem pos) o st' c ∧
      (o.value = (SplayState.leftmostWalk P st k x).2 ∧
        Lay.NodesAt st'.mem nb cap (SplayState.leftmostWalk P st k x).1 ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧
      0 + c ≤ (walkSteps P st k x + 1) * (pushDownCost S + 80)
  | 0, x, pos, mem, st, hnodes, hptr, hx, hheap, hk, hok => by
    have hwide := hheap.wide
    unfold leftmostWalkBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step
    · wram_step
      · exact ⟨by simp [SplayState.leftmostWalk, Outcome.value],
          by simpa [SplayState.leftmostWalk] using hnodes, TreeFrame.refl hheap.zero⟩
      · simp only [walkSteps, pushDownCost]; wram_cost
  | k + 1, x, pos, mem, st, hnodes, hptr, hx, hheap, hk, hok => by
    have hroom := hheap.room
    have hwide := hheap.wide
    have hS := hheap.stride_lt
    have hS6 := Lay.stride_pos
    have hA := hheap.addr_lt hx
    have hxS : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
    set C := pushDownCost S with hC
    have hT := Nat.le_mul_of_pos_left (C + 80) (by omega : 0 < walkSteps P st (k + 1) x + 1)
    unfold nodeAddr at hA
    unfold leftmostWalkBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step
    wram_step
    · subst hcond
      wram_step
      · exact ⟨by simp [SplayState.leftmostWalk, Outcome.value],
          by simpa [SplayState.leftmostWalk] using hnodes, TreeFrame.refl hheap.zero⟩
      · simp only [hC, pushDownCost] at *; wram_cost
    have hx0 : x ≠ 0 := hcond
    obtain ⟨okD, okW⟩ := hok hx0
    set st₁ := SplayState.pushDown P st x with hst₁
    refine runs_seq_callBody_le L.pushDown_body (by eval_expr)
      (R := fun _ m₁ c₁ => Lay.NodesAt m₁.mem nb cap st₁ ∧
        TreeFrame Lay nb cap heap mem m₁.mem ∧ c₁ ≤ C) ?_ ?_
    · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := pushDownBody_runs L ω hnodes hptr hx hheap okD
      exact ⟨o, st', c, hr, hn, hf, by omega⟩
    rintro - m₁ c₁ ⟨hn₁, hf₁, hc₁⟩
    have hp₁ : PtrOk cap st₁ := hptr.pushDown hx
    have hlc := (hp₁ x hx).1
    set l := (st₁.nodes x).left with hl
    have hm0 : m₁.mem (nb + Lay.nodeStride * x) = l := (hn₁ x hx).1
    wram_step; try dsimp only
    rw [hm0]
    wram_step
    · have hl0 : l = 0 := hcond
      wram_step
      · refine ⟨?_, ?_, hf₁⟩
        · simp [SplayState.leftmostWalk, hx0, ← hst₁, ← hl, hl0, Outcome.value]
        · simpa [SplayState.leftmostWalk, hx0, ← hst₁, ← hl, hl0] using hn₁
      · simp only [hC, pushDownCost] at *; wram_cost
    have hl0 : l ≠ 0 := hcond
    have hsteps : walkSteps P st (k + 1) x = 1 + walkSteps P st₁ k l := by
      simp [walkSteps, hx0, ← hst₁, ← hl, hl0]
    have hwalk : SplayState.leftmostWalk P st (k + 1) x = SplayState.leftmostWalk P st₁ k l := by
      simp [SplayState.leftmostWalk, hx0, ← hst₁, ← hl, hl0]
    have hlS : l ≤ Lay.nodeStride * l := Nat.le_mul_of_pos_left l (by omega)
    have hAl := hheap.addr_lt hlc
    unfold nodeAddr at hAl
    refine runs_seq_callBody_le hself (by eval_expr)
      (R := fun v m₂ c₂ => v = (SplayState.leftmostWalk P st₁ k l).2 ∧
        Lay.NodesAt m₂.mem nb cap (SplayState.leftmostWalk P st₁ k l).1 ∧
        TreeFrame Lay nb cap heap mem m₂.mem ∧ c₂ ≤ (walkSteps P st₁ k l + 1) * (C + 80)) ?_ ?_
    · obtain ⟨o, st', c, hr, ⟨hv, hn, hf⟩, hc⟩ := leftmostWalkBody_runs L hself ω k l _ hn₁ hp₁
        hlc ⟨hheap.rec_le, hroom, hf₁.1, hwide⟩ (by omega) okW
      simp only [← hC] at hc
      exact ⟨o, st', c, by simpa using hr, hv, hn, hf₁.trans hf, by omega⟩
    rintro v₂ m₂ c₂ ⟨hv₂, hn₂, hf₂, hc₂⟩
    wram_step
    · refine ⟨?_, ?_, hf₂⟩
      · simp [Outcome.value, hwalk, hv₂]
      · rw [hwalk]; exact hn₂
    · rw [hsteps] at hT ⊢
      have : (1 + walkSteps P st₁ k l + 1) * (C + 80) =
          (walkSteps P st₁ k l + 1) * (C + 80) + (C + 80) := by ring
      rw [this]
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
        argsSize_cons, argsSize_nil] at *
      omega

end MinCostFlow.LinkCut.Gen
