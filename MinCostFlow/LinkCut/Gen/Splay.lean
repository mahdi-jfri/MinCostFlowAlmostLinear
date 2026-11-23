module

public import MinCostFlow.LinkCut.Gen.Rotate

/-!
# `splayStep`, `splayLoop` and `splay` as programs

`splayStepBody` is the machine version of `SplayState.splayStep` (a zig, zig-zig or zig-zag
step, made of calls to `rotate`). `splayLoopBody` is the machine version of
`SplayState.splayLoop`, a recursive procedure with the fuel as an argument; its cost is at most
`splayLoopSteps st fuel x + 1` times the cost of one step, where `splayLoopSteps` counts the
steps the model takes. `splayBody` runs `pushPath` and then `splayLoop`, as `SplayState.splay`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

theorem PtrOk.rotate {cap x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.rotate P st x) := by
  by_cases hx0 : x = 0
  · simpa [SplayState.rotate, hx0] using h
  by_cases hp0 : (st.nodes x).par = 0
  · simpa [SplayState.rotate, hx0, hp0] using h
  rw [rotate_eq hx0 hp0]
  exact ((h.rotateMid hx).pull (h x hx).2.2.1).pull hx

theorem PtrOk.splayStep {cap x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.splayStep P st x) := by
  have hp := (h x hx).2.2.1
  unfold SplayState.splayStep
  dsimp only
  split_ifs
  · exact h
  · exact h
  · exact h.rotate hx
  · exact (h.rotate hp).rotate hx
  · exact (h.rotate hx).rotate hx

/-! ### `splayStep` -/

/-- `splayStep` on `[nb, x, heap]`; `rotProc` is `rotate`. -/
def splayStepBody (rotProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 3 (recAddr 1) ;;
     .assign 4 (.load (.bin .add (.reg 3) (.const 2))) ;;
     .cond (.bin .eq (.reg 4) (.const 0)) (.ret (.const 0))
       (.assign 5 (recAddr 4) ;;
        .assign 6 (.load (.bin .add (.reg 5) (.const 2))) ;;
        .cond (.bin .eq (.reg 6) (.const 0))
          (.call 7 rotProc [.reg 0, .reg 1, .reg 2] ;; .ret (.const 0))
          (.assign 8 (.bin .eq (.reg 1) (.load (.reg 5))) ;;
           .assign 9 (.bin .eq (.reg 4) (.load (recAddr 6))) ;;
           .cond (.bin .eq (.reg 8) (.reg 9))
             (.call 7 rotProc [.reg 0, .reg 4, .reg 2])
             (.call 7 rotProc [.reg 0, .reg 1, .reg 2]) ;;
           .call 7 rotProc [.reg 0, .reg 1, .reg 2] ;;
           .ret (.const 0))))

theorem splayStepBody_noRand (rotProc : ℕ) :
    (splayStepBody rotProc).NoRand := by
  simp [splayStepBody, recAddr, Stmt.NoRand]

/-- The summaries that `splayStep P st x` computes are representable. -/
def SplayStepOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) :
    Prop :=
  let p := (st.nodes x).par
  let g := (st.nodes p).par
  if g = 0 then RotateOk ok P st x
  else if (x == (st.nodes p).left) == (p == (st.nodes g).left) then
    RotateOk ok P st p ∧ RotateOk ok P (SplayState.rotate P st p) x
  else RotateOk ok P st x ∧ RotateOk ok P (SplayState.rotate P st x) x

/-- A bound on the cost of one `splayStep` call. -/
def splayStepCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) : ℕ :=
  2 * rotateCost S + 100

/-- The run of `splayStepBody`. -/
theorem splayStepBody_runs {w nb cap x heap pos pullProc rotProc : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (hpull : p.procs[pullProc]? = some (pullBody S.pull))
    (hrot : p.procs[rotProc]? = some (rotateBody pullProc))
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap S.space mem) (hok : SplayStepOk ok P st x) :
    ∃ o st' c, Runs w p ω (splayStepBody rotProc) (startState [nb, x, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.splayStep P st x) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧ 0 + c ≤ splayStepCost S := by
  have hroom := hheap.room
  have hwide := hheap.wide
  have hS := hheap.stride_lt
  have hS6 := Lay.stride_pos
  have hrec := hheap.rec_le
  have hlt : ∀ y ≤ cap, nb + Lay.nodeStride * y + Lay.nodeStride ≤ heap := fun y hy => by
    have := hheap.addr_lt hy; unfold nodeAddr at this; exact this
  have hyw : ∀ y ≤ cap, y < 2 ^ w := fun y hy => by
    have := hlt y hy
    have : y ≤ Lay.nodeStride * y := Nat.le_mul_of_pos_left y (by omega)
    omega
  obtain ⟨-, -, hpc, -⟩ := hptr x hx
  set pa := (st.nodes x).par with hpa
  obtain ⟨-, -, hgc, -⟩ := hptr pa hpc
  set g := (st.nodes pa).par with hg
  have hm2 : mem (nb + Lay.nodeStride * x + 2) = pa := (hnodes x hx).2.2.1
  have hmB : mem (nb + Lay.nodeStride * pa) = (st.nodes pa).left := (hnodes pa hpc).1
  have hmB2 : mem (nb + Lay.nodeStride * pa + 2) = g := (hnodes pa hpc).2.2.1
  have hmG : mem (nb + Lay.nodeStride * g) = (st.nodes g).left := (hnodes g hgc).1
  have hAx := hlt x hx
  have hApa := hlt pa hpc
  have hAg := hlt g hgc
  have hxw := hyw x hx
  have hpw := hyw pa hpc
  -- a call of `rotate` at `y`, then the rest
  have hcall : ∀ (st₁ : State) (s₁ : SplayState α σ τ) (y : ℕ) (r : ℕ) (rest : Stmt) (k T : ℕ)
      (Q : Outcome → State → Prop), st₁.regs 0 = nb → st₁.regs r = y → st₁.regs 2 = heap →
      Lay.NodesAt st₁.mem nb cap s₁ → PtrOk cap s₁ → y ≤ cap →
      TreeFrame Lay nb cap heap mem st₁.mem → RotateOk ok P s₁ y →
      (∀ (v : ℕ) (st₂ : State) (c₂ : ℕ), Lay.NodesAt st₂.mem nb cap (SplayState.rotate P s₁ y) →
        TreeFrame Lay nb cap heap mem st₂.mem → c₂ ≤ rotateCost S →
        ∃ o st' c, Runs w p ω rest { st₂ with regs := Function.update st₁.regs 7 v } o st' c ∧
          Q o st' ∧ (k + 5 + c₂) + c ≤ T) →
      ∃ o st' c, Runs w p ω (.seq (.call 7 rotProc [.reg 0, .reg r, .reg 2]) rest) st₁ o st' c ∧
        Q o st' ∧ k + c ≤ T := by
    intro st₁ s₁ y r rest k T Q h0 hr h2 hn₁ hp₁ hy hf₁ hok₁ hrest
    refine runs_seq_callBody_le hrot (by eval_expr)
      (R := fun _ st₂ c₂ => Lay.NodesAt st₂.mem nb cap (SplayState.rotate P s₁ y) ∧
        TreeFrame Lay nb cap heap mem st₂.mem ∧ c₂ ≤ rotateCost S) ?_ ?_
    · obtain ⟨o, st', c, hrun, ⟨hn, hf⟩, hc⟩ := rotateBody_runs S hpull ω hn₁ hp₁ hy
        ⟨hrec, hroom, hf₁.1, hwide⟩ hok₁
      exact ⟨o, st', c, hrun, hn, hf₁.trans hf, by omega⟩
    rintro v st₂ c₂ ⟨hn₂, hf₂, hc₂⟩
    obtain ⟨o, st', c, hrun, hq, hc⟩ := hrest v st₂ c₂ hn₂ hf₂ hc₂
    exact ⟨o, st', c, hrun, hq, by simp only [argsSize_cons, argsSize_nil, Expr.size_reg] at *; omega⟩
  have hR2 := Nat.le_refl (rotateCost S)
  unfold splayStepBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [SplayState.splayStep] using hnodes, TreeFrame.refl hheap.zero⟩
    · simp only [splayStepCost, rotateCost]; wram_cost
  have hx0 : x ≠ 0 := hcond
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hm2]
  wram_step
  · have hp0 : pa = 0 := hcond
    wram_step
    · exact ⟨by simpa [SplayState.splayStep, hx0, ← hpa, hp0] using hnodes,
        TreeFrame.refl hheap.zero⟩
    · simp only [splayStepCost, rotateCost]; wram_cost
  have hp0 : pa ≠ 0 := hcond
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hmB2]
  wram_step
  · -- zig
    have hg0 : g = 0 := hcond
    have hok' : RotateOk ok P st x := by simpa [SplayStepOk, ← hpa, ← hg, hg0] using hok
    refine hcall _ st x 1 _ _ _ _ (by simp) (by simp) (by simp) hnodes hptr hx
      (TreeFrame.refl hheap.zero) hok' fun v st₂ c₂ hn₂ hf₂ hc₂ => ?_
    wram_step
    · refine ⟨?_, hf₂⟩
      have : SplayState.splayStep P st x = SplayState.rotate P st x := by
        simp [SplayState.splayStep, hx0, ← hpa, hp0, ← hg, hg0]
      rw [this]; exact hn₂
    · simp only [splayStepCost] at *; wram_cost
  have hg0 : g ≠ 0 := hcond
  wram_step; try dsimp only
  rw [hmB]
  wram_step; try dsimp only
  rw [hmG]
  have hiff : ((if x = (st.nodes pa).left then 1 else 0) = (if pa = (st.nodes g).left then 1 else 0))
      ↔ ((x == (st.nodes pa).left) == (pa == (st.nodes g).left)) = true := by
    by_cases h1 : x = (st.nodes pa).left <;> by_cases h2 : pa = (st.nodes g).left <;> simp [h1, h2]
  refine runs_seq_cond_le (by eval_expr) (fun hc => ?_) (fun hc => ?_)
  · -- zig-zig
    have hc' : ((x == (st.nodes pa).left) == (pa == (st.nodes g).left)) = true := by
      rw [← hiff]; by_contra h; simp [h] at hc
    have hok' : RotateOk ok P st pa ∧ RotateOk ok P (SplayState.rotate P st pa) x := by
      simpa [SplayStepOk, ← hpa, ← hg, hg0, hc'] using hok
    refine hcall _ st pa 4 _ _ _ _ (by simp) (by simp) (by simp) hnodes hptr hpc
      (TreeFrame.refl hheap.zero) hok'.1 fun v st₂ c₂ hn₂ hf₂ hc₂ => ?_
    refine hcall _ _ x 1 _ _ _ _ (by simp) (by simp) (by simp) hn₂ (hptr.rotate hpc) hx
      hf₂ hok'.2 fun v' st₃ c₃ hn₃ hf₃ hc₃ => ?_
    wram_step
    · refine ⟨?_, hf₃⟩
      have : SplayState.splayStep P st x =
          SplayState.rotate P (SplayState.rotate P st pa) x := by
        simp only [SplayState.splayStep, hx0, ← hpa, hp0, ← hg, hg0, hc', if_false, if_true]
      rw [this]; exact hn₃
    · simp only [splayStepCost] at *; wram_cost
  · -- zig-zag
    have hc' : ((x == (st.nodes pa).left) == (pa == (st.nodes g).left)) = false := by
      by_contra h
      simp only [Bool.not_eq_false] at h
      rw [← hiff] at h; simp [h] at hc
    have hok' : RotateOk ok P st x ∧ RotateOk ok P (SplayState.rotate P st x) x := by
      simpa [SplayStepOk, ← hpa, ← hg, hg0, hc'] using hok
    refine hcall _ st x 1 _ _ _ _ (by simp) (by simp) (by simp) hnodes hptr hx
      (TreeFrame.refl hheap.zero) hok'.1 fun v st₂ c₂ hn₂ hf₂ hc₂ => ?_
    refine hcall _ _ x 1 _ _ _ _ (by simp) (by simp) (by simp) hn₂ (hptr.rotate hx) hx
      hf₂ hok'.2 fun v' st₃ c₃ hn₃ hf₃ hc₃ => ?_
    wram_step
    · refine ⟨?_, hf₃⟩
      have : SplayState.splayStep P st x =
          SplayState.rotate P (SplayState.rotate P st x) x := by
        simp only [SplayState.splayStep, hx0, ← hpa, hp0, ← hg, hg0, hc', if_false]
        rfl
      rw [this]; exact hn₃
    · simp only [splayStepCost] at *; wram_cost

/-! ### `splayLoop` -/

/-- The number of steps `SplayState.splayLoop P st fuel x` takes. -/
def splayLoopSteps (P : LctPayload α σ τ) (st : SplayState α σ τ) : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, x =>
      if x = 0 then 0
      else if (st.nodes x).par = 0 then 0
      else 1 + splayLoopSteps P (SplayState.splayStep P st x) k x

/-- The summaries that `splayLoop P st fuel x` computes are representable. -/
def SplayLoopOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) :
    SplayState α σ τ → ℕ → ℕ → Prop
  | _, 0, _ => True
  | st, k + 1, x => x ≠ 0 → (st.nodes x).par ≠ 0 →
      SplayStepOk ok P st x ∧ SplayLoopOk ok P (SplayState.splayStep P st x) k x

theorem PtrOk.splayLoop {cap : ℕ} {P : LctPayload α σ τ} :
    ∀ (k x : ℕ) {st : SplayState α σ τ}, PtrOk cap st → x ≤ cap →
      PtrOk cap (SplayState.splayLoop P st k x)
  | 0, _, _, h, _ => h
  | k + 1, x, st, h, hx => by
    unfold SplayState.splayLoop
    split_ifs
    · exact h
    · exact h
    · exact PtrOk.splayLoop k x (h.splayStep hx) hx

/-- `splayLoop` on `[nb, x, fuel, heap]`; `selfProc` is this procedure and `stepProc` is
`splayStep`. -/
def splayLoopBody (selfProc stepProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 0))
    (.cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
      (.cond (.bin .eq (.load (.bin .add (recAddr 1) (.const 2))) (.const 0)) (.ret (.const 0))
        (.call 4 stepProc [.reg 0, .reg 1, .reg 3] ;;
         .call 4 selfProc [.reg 0, .reg 1, .bin .sub (.reg 2) (.const 1), .reg 3] ;;
         .ret (.const 0))))

theorem splayLoopBody_noRand (selfProc stepProc : ℕ) :
    (splayLoopBody selfProc stepProc).NoRand := by
  simp [splayLoopBody, recAddr, Stmt.NoRand]

/-- The run of `splayLoopBody`. -/
theorem splayLoopBody_runs {w nb cap heap pullProc rotProc stepProc loopProc : ℕ}
    {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (hpull : p.procs[pullProc]? = some (pullBody S.pull))
    (hrot : p.procs[rotProc]? = some (rotateBody pullProc))
    (hstep : p.procs[stepProc]? = some (splayStepBody rotProc))
    (hself : p.procs[loopProc]? = some (splayLoopBody loopProc stepProc)) (ω : ℕ → Bool) :
    ∀ (k x pos : ℕ) {mem : ℕ → ℕ} {st : SplayState α σ τ},
    Lay.NodesAt mem nb cap st → PtrOk cap st → x ≤ cap →
    HeapOk Lay w nb cap heap S.space mem → k < 2 ^ w → SplayLoopOk ok P st k x →
    ∃ o st' c, Runs w p ω (splayLoopBody loopProc stepProc)
        (startState [nb, x, k, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.splayLoop P st k x) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧
      0 + c ≤ (splayLoopSteps P st k x + 1) * (splayStepCost S + 60)
  | 0, x, pos, mem, st, hnodes, hptr, hx, hheap, hk, hok => by
    have hwide := hheap.wide
    unfold splayLoopBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step
    · wram_step
      · exact ⟨by simpa [SplayState.splayLoop] using hnodes, TreeFrame.refl hheap.zero⟩
      · simp only [splayLoopSteps, splayStepCost, rotateCost]; wram_cost
  | k + 1, x, pos, mem, st, hnodes, hptr, hx, hheap, hk, hok => by
    have hroom := hheap.room
    have hwide := hheap.wide
    have hS := hheap.stride_lt
    have hS6 := Lay.stride_pos
    have hA := hheap.addr_lt hx
    have hxS : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
    have hm2 : mem (nb + Lay.nodeStride * x + 2) = (st.nodes x).par := (hnodes x hx).2.2.1
    set C := splayStepCost S with hC
    have hT := Nat.le_mul_of_pos_left (C + 60) (by omega : 0 < splayLoopSteps P st (k + 1) x + 1)
    unfold nodeAddr at hA
    unfold splayLoopBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step
    wram_step
    · subst hcond
      wram_step
      · exact ⟨by simpa [SplayState.splayLoop] using hnodes, TreeFrame.refl hheap.zero⟩
      · simp only [hC, splayStepCost, rotateCost] at *; wram_cost
    have hx0 : x ≠ 0 := hcond
    wram_step
    · have hp0 : (st.nodes x).par = 0 := hm2 ▸ hcond
      wram_step
      · exact ⟨by simpa [SplayState.splayLoop, hx0, hp0] using hnodes, TreeFrame.refl hheap.zero⟩
      · simp only [hC, splayStepCost, rotateCost] at *; wram_cost
    · have hp0 : (st.nodes x).par ≠ 0 := hm2 ▸ hcond
      obtain ⟨okS, okL⟩ := hok hx0 hp0
      have hsteps : splayLoopSteps P st (k + 1) x =
          1 + splayLoopSteps P (SplayState.splayStep P st x) k x := by
        simp [splayLoopSteps, hx0, hp0]
      refine runs_seq_callBody_le hstep (by eval_expr)
        (R := fun _ st₁ c₁ => Lay.NodesAt st₁.mem nb cap (SplayState.splayStep P st x) ∧
          TreeFrame Lay nb cap heap mem st₁.mem ∧ c₁ ≤ C) ?_ ?_
      · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := splayStepBody_runs S hpull hrot ω hnodes hptr hx
          hheap okS
        exact ⟨o, st', c, hr, hn, hf, by omega⟩
      rintro v₁ st₁ c₁ ⟨hn₁, hf₁, hc₁⟩
      refine runs_seq_callBody_le hself (by eval_expr)
        (R := fun _ st₂ c₂ => Lay.NodesAt st₂.mem nb cap (SplayState.splayLoop P st (k + 1) x) ∧
          TreeFrame Lay nb cap heap mem st₂.mem ∧
          c₂ ≤ (splayLoopSteps P (SplayState.splayStep P st x) k x + 1) * (C + 60)) ?_ ?_
      · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := splayLoopBody_runs S hpull hrot hstep hself ω k x
          _ hn₁ (hptr.splayStep hx) hx ⟨hheap.rec_le, hroom, hf₁.1, hwide⟩ (by omega) okL
        simp only [← hC] at hc
        refine ⟨o, st', c, by simpa using hr, ?_, hf₁.trans hf, by omega⟩
        have : SplayState.splayLoop P st (k + 1) x =
            SplayState.splayLoop P (SplayState.splayStep P st x) k x := by
          simp [SplayState.splayLoop, hx0, hp0]
        rw [this]; exact hn
      rintro v₂ st₂ c₂ ⟨hn₂, hf₂, hc₂⟩
      wram_step
      · exact ⟨hn₂, hf₂⟩
      · rw [hsteps] at hT ⊢
        have : (1 + splayLoopSteps P (SplayState.splayStep P st x) k x + 1) * (C + 60) =
            (splayLoopSteps P (SplayState.splayStep P st x) k x + 1) * (C + 60) + (C + 60) := by
          ring
        rw [this]
        simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
          argsSize_cons, argsSize_nil] at *
        omega

/-! ### `splay` -/

/-- The payload values that `splay P st fuel x` computes are representable. -/
def SplayOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : SplayState α σ τ)
    (fuel x : ℕ) : Prop :=
  x ≠ 0 → PushPathOk ok P st fuel x ∧
    SplayLoopOk ok P (SplayState.pushPath P st fuel x) fuel x

theorem PtrOk.splay {cap fuel x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.splay P st fuel x) := by
  unfold SplayState.splay
  split_ifs
  · exact h
  · exact PtrOk.splayLoop fuel x (h.pushPath fuel x hx) hx

/-- The cost bound of `splay P st fuel x`. -/
def splayCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) (st : SplayState α σ τ)
    (fuel x : ℕ) : ℕ :=
  (splayDepth st fuel x + 1) * (pushDownCost S + 80) +
    (splayLoopSteps P (SplayState.pushPath P st fuel x) fuel x + 1) * (splayStepCost S + 60) + 40

/-- `splay` on `[nb, x, fuel, heap]`: `pushPath`, then `splayLoop`. -/
def splayBody (ppProc loopProc : ℕ) : Stmt :=
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.call 4 ppProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
     .call 4 loopProc [.reg 0, .reg 1, .reg 2, .reg 3] ;;
     .ret (.const 0))

theorem splayBody_noRand (ppProc loopProc : ℕ) : (splayBody ppProc loopProc).NoRand := by
  simp [splayBody, Stmt.NoRand]

/-- The procedures `splay` needs, at their indices in the program. -/
structure SplayProcs {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} {S : PayloadSteps w p P Lay ok} (L : LazyProcs w p P Lay ok S) where
  pull : ℕ
  rotate : ℕ
  step : ℕ
  loop : ℕ
  pushPath : ℕ
  splay : ℕ
  pull_body : p.procs[pull]? = some (pullBody S.pull)
  rotate_body : p.procs[rotate]? = some (rotateBody pull)
  step_body : p.procs[step]? = some (splayStepBody rotate)
  loop_body : p.procs[loop]? = some (splayLoopBody loop step)
  pushPath_body : p.procs[pushPath]? = some (pushPathBody pushPath L.pushDown)
  splay_body : p.procs[splay]? = some (splayBody pushPath loop)

/-- The run of `splayBody`. -/
theorem splayBody_runs {w nb cap heap fuel x pos : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    {S : PayloadSteps w p P Lay ok} {L : LazyProcs w p P Lay ok S} (Q : SplayProcs L)
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem) (hk : fuel < 2 ^ w)
    (hok : SplayOk ok P st fuel x) :
    ∃ o st' c, Runs w p ω (splayBody Q.pushPath Q.loop)
        (startState [nb, x, fuel, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.splay P st fuel x) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧
      0 + c ≤ splayCost S st fuel x := by
  have hwide := hheap.wide
  unfold splayBody
  rw [startState]
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [SplayState.splay] using hnodes, TreeFrame.refl hheap.zero⟩
    · simp only [splayCost]; wram_cost
  have hx0 : x ≠ 0 := hcond
  obtain ⟨okP, okL⟩ := hok hx0
  refine runs_seq_callBody_le Q.pushPath_body (by eval_expr)
    (R := fun _ st₁ c₁ => Lay.NodesAt st₁.mem nb cap (SplayState.pushPath P st fuel x) ∧
      TreeFrame Lay nb cap heap mem st₁.mem ∧
      c₁ ≤ (splayDepth st fuel x + 1) * (pushDownCost S + 80)) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := pushPathBody_runs L Q.pushPath_body ω fuel x
      pos hnodes hptr hx hheap hk okP
    exact ⟨o, st', c, by simpa using hr, hn, hf, by omega⟩
  rintro v₁ st₁ c₁ ⟨hn₁, hf₁, hc₁⟩
  refine runs_seq_callBody_le Q.loop_body (by eval_expr)
    (R := fun _ st₂ c₂ => Lay.NodesAt st₂.mem nb cap (SplayState.splay P st fuel x) ∧
      TreeFrame Lay nb cap heap mem st₂.mem ∧
      c₂ ≤ (splayLoopSteps P (SplayState.pushPath P st fuel x) fuel x + 1) *
        (splayStepCost S + 60)) ?_ ?_
  · have hheap₁ : HeapOk Lay w nb cap heap S.space st₁.mem :=
      ⟨hheap.rec_le, by have := hheap.room; omega, hf₁.1, hwide⟩
    obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := splayLoopBody_runs S Q.pull_body Q.rotate_body
      Q.step_body Q.loop_body ω fuel x _ hn₁ (hptr.pushPath fuel x hx) hx hheap₁ hk okL
    refine ⟨o, st', c, by simpa using hr, ?_, hf₁.trans hf, by omega⟩
    simpa [SplayState.splay, hx0] using hn
  rintro v₂ st₂ c₂ ⟨hn₂, hf₂, hc₂⟩
  wram_step
  · exact ⟨hn₂, hf₂⟩
  · simp only [splayCost]
    simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, argsSize_cons, argsSize_nil] at *
    omega

end MinCostFlow.LinkCut.Gen
