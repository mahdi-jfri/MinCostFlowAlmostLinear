module

public import MinCostFlow.LinkCut.Gen.PushPath

/-!
# `rotate` as a program

`rotateBody` is the machine version of `SplayState.rotate`: it moves node `x` above its parent
`p`, with the same eight pointer writes as the model, and then calls `pull` on `p` and on `x`.
The side of a child is a number `0` (left) or `1` (right), so each write of a child pointer is a
single store at offset `0` or `1` (`NodesAt.setSide`). The arguments are `[nb, x, heap]`.

`rotateMid P st x` is the state of the model before the two pulls (`rotate_eq`).
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-- The pointer writes of `SplayState.rotate`, before the two pulls. -/
def rotateMid (st : SplayState α σ τ) (x : ℕ) : SplayState α σ τ :=
  let p := (st.nodes x).par
  let g := (st.nodes p).par
  let pp := (st.nodes p).ppar
  let isLeft := (x == (st.nodes p).left)
  let b := if isLeft then (st.nodes x).right else (st.nodes x).left
  let st1 := if isLeft then st.setRight x p else st.setLeft x p
  let st2 := if isLeft then st1.setLeft p b else st1.setRight p b
  let st3 := if b = 0 then st2 else st2.setPar b p
  let st4 := st3.setPar p x
  let st5 := st4.setPar x g
  let st6 := st5.setPpar x pp
  let st7 := st6.setPpar p 0
  if g = 0 then st7
  else if p == (st7.nodes g).left then st7.setLeft g x
  else st7.setRight g x

theorem rotate_eq {P : LctPayload α σ τ} {st : SplayState α σ τ} {x : ℕ} (hx : x ≠ 0)
    (hp : (st.nodes x).par ≠ 0) :
    SplayState.rotate P st x =
      SplayState.pull P (SplayState.pull P (rotateMid st x) (st.nodes x).par) x := by
  simp only [SplayState.rotate, rotateMid, hx, hp, if_false]

theorem PtrOk.setLeft {cap x v : ℕ} {st : SplayState α σ τ} (h : PtrOk cap st) (hx : x ≤ cap)
    (hv : v ≤ cap) : PtrOk cap (st.setLeft x v) :=
  h.updateNode_ptrs (by have := h x hx; simp only; omega)

theorem PtrOk.setRight {cap x v : ℕ} {st : SplayState α σ τ} (h : PtrOk cap st) (hx : x ≤ cap)
    (hv : v ≤ cap) : PtrOk cap (st.setRight x v) :=
  h.updateNode_ptrs (by have := h x hx; simp only; omega)

theorem PtrOk.setPar {cap x v : ℕ} {st : SplayState α σ τ} (h : PtrOk cap st) (hx : x ≤ cap)
    (hv : v ≤ cap) : PtrOk cap (st.setPar x v) :=
  h.updateNode_ptrs (by have := h x hx; simp only; omega)

theorem PtrOk.setPpar {cap x v : ℕ} {st : SplayState α σ τ} (h : PtrOk cap st) (hx : x ≤ cap)
    (hv : v ≤ cap) : PtrOk cap (st.setPpar x v) :=
  h.updateNode_ptrs (by have := h x hx; simp only; omega)

theorem PtrOk.rotateMid {cap x : ℕ} {st : SplayState α σ τ} (h : PtrOk cap st) (hx : x ≤ cap) :
    PtrOk cap (Gen.rotateMid st x) := by
  obtain ⟨hl, hr, hp, -⟩ := h x hx
  obtain ⟨-, -, hg, hpp⟩ := h _ hp
  unfold Gen.rotateMid
  dsimp only
  split_ifs <;>
    (repeat' (first | assumption | exact Nat.zero_le _ | apply PtrOk.setLeft |
      apply PtrOk.setRight | apply PtrOk.setPar | apply PtrOk.setPpar))

/-- `rotate` on `[nb, x, heap]`. -/
def rotateBody (pullProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
    (.assign 3 (recAddr 1) ;;
     .assign 4 (.load (.bin .add (.reg 3) (.const 2))) ;;
     .cond (.bin .eq (.reg 4) (.const 0)) (.ret (.const 0))
       (.assign 5 (recAddr 4) ;;
        .assign 6 (.load (.bin .add (.reg 5) (.const 2))) ;;
        .assign 7 (.load (.bin .add (.reg 5) (.const 3))) ;;
        .assign 8 (.bin .eq (.reg 1) (.load (.reg 5))) ;;
        .assign 9 (.load (.bin .add (.reg 3) (.reg 8))) ;;
        .store (.bin .add (.reg 3) (.reg 8)) (.reg 4) ;;
        .store (.bin .add (.reg 5) (.bin .sub (.const 1) (.reg 8))) (.reg 9) ;;
        .cond (.reg 9) (.store (.bin .add (recAddr 9) (.const 2)) (.reg 4)) .nop ;;
        .store (.bin .add (.reg 5) (.const 2)) (.reg 1) ;;
        .store (.bin .add (.reg 3) (.const 2)) (.reg 6) ;;
        .store (.bin .add (.reg 3) (.const 3)) (.reg 7) ;;
        .store (.bin .add (.reg 5) (.const 3)) (.const 0) ;;
        .assign 10 (recAddr 6) ;;
        .assign 11 (.bin .eq (.reg 4) (.load (.reg 10))) ;;
        .cond (.reg 6) (.store (.bin .add (.reg 10) (.bin .sub (.const 1) (.reg 11))) (.reg 1))
          .nop ;;
        .call 12 pullProc [.reg 0, .reg 4, .reg 2] ;;
        .call 12 pullProc [.reg 0, .reg 1, .reg 2] ;;
        .ret (.const 0)))

theorem rotateBody_noRand (pullProc : ℕ) :
    (rotateBody pullProc).NoRand := by
  simp [rotateBody, recAddr, Stmt.NoRand]

/-- The summaries that `rotate P st x` computes are representable. -/
def RotateOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : SplayState α σ τ) (x : ℕ) :
    Prop :=
  x ≠ 0 → (st.nodes x).par ≠ 0 →
    ok.sumOk (pullSum P (rotateMid st x) (st.nodes x).par) ∧
    ok.sumOk (pullSum P (SplayState.pull P (rotateMid st x) (st.nodes x).par) x)

/-- A bound on the cost of one `rotate` call. -/
def rotateCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) : ℕ :=
  2 * S.cost + 600

/-- The run of `rotateBody`. -/
theorem rotateBody_runs {w nb cap x heap pos pullProc : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    (S : PayloadSteps w p P Lay ok) (hpull : p.procs[pullProc]? = some (pullBody S.pull))
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap S.space mem) (hok : RotateOk ok P st x) :
    ∃ o st' c, Runs w p ω (rotateBody pullProc) (startState [nb, x, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.rotate P st x) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧ 0 + c ≤ rotateCost S := by
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
  obtain ⟨hxl, hxr, hpc, -⟩ := hptr x hx
  set pa := (st.nodes x).par with hpa
  obtain ⟨-, -, hgc, hppc⟩ := hptr pa hpc
  set g := (st.nodes pa).par with hg
  set pp := (st.nodes pa).ppar with hpp
  have hm2 : mem (nb + Lay.nodeStride * x + 2) = pa := (hnodes x hx).2.2.1
  have hmB : mem (nb + Lay.nodeStride * pa) = (st.nodes pa).left := (hnodes pa hpc).1
  have hmB2 : mem (nb + Lay.nodeStride * pa + 2) = g := (hnodes pa hpc).2.2.1
  have hmB3 : mem (nb + Lay.nodeStride * pa + 3) = pp := (hnodes pa hpc).2.2.2.1
  have hAx := hlt x hx
  have hApa := hlt pa hpc
  have hAg := hlt g hgc
  unfold rotateBody
  rw [startState]
  refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
  wram_step
  · subst hcond
    wram_step
    · exact ⟨by simpa [SplayState.rotate] using hnodes, TreeFrame.refl hheap.zero⟩
    · simp only [rotateCost]; wram_cost
  have hx0 : x ≠ 0 := hcond
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hm2]
  wram_step
  · have hp0 : pa = 0 := hcond
    wram_step
    · exact ⟨by simpa [SplayState.rotate, hx0, ← hpa, hp0] using hnodes,
        TreeFrame.refl hheap.zero⟩
    · simp only [rotateCost]; wram_cost
  have hp0 : pa ≠ 0 := hcond
  wram_step; try dsimp only
  wram_step; try dsimp only
  rw [hmB2]
  wram_step; try dsimp only
  rw [hmB3]
  wram_step; try dsimp only
  rw [hmB]
  set isLeft := (x == (st.nodes pa).left) with hisLeft
  have hil : (if x = (st.nodes pa).left then 1 else 0) = (if isLeft then 1 else 0) := by
    simp [isLeft]
  rw [hil]
  have hbc : (if isLeft then (st.nodes x).right else (st.nodes x).left) ≤ cap := by
    split_ifs <;> assumption
  have hmb : mem (nb + Lay.nodeStride * x + if isLeft then 1 else 0) =
      (if isLeft then (st.nodes x).right else (st.nodes x).left) := by
    split_ifs
    · exact (hnodes x hx).2.1
    · exact (hnodes x hx).1
  have hil1 : (if isLeft then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h1il : 1 - (if isLeft then 1 else 0) = (if (!isLeft) = true then 1 else 0) := by
    rcases Bool.eq_false_or_eq_true isLeft with h | h <;> simp [h]
  generalize hb_eq : (if isLeft then (st.nodes x).right else (st.nodes x).left) = b at hbc hmb
  generalize hil_eq : (if isLeft then 1 else 0) = il at hil1 hmb h1il ⊢
  wram_step; try dsimp only
  rw [hmb]
  have hAb := hlt b hbc
  -- st1: the child of `x` on the side of `p` becomes `p`
  set st₁ := if isLeft then st.setRight x pa else st.setLeft x pa with hst₁
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₁ hM₁ => ?_
  have hN₁ : Lay.NodesAt M₁ nb cap st₁ := by
    rw [hM₁, ← hil_eq]; exact hnodes.setSide Lay hx isLeft
  have hF₁ : TreeFrame Lay nb cap heap mem M₁ := by
    rw [hM₁]; exact TreeFrame.of_ctrl hx (by omega) hAx hheap.zero
  -- st2: the child of `p` on the side of `x` becomes `b`
  set st₂ := if isLeft then st₁.setLeft pa b else st₁.setRight pa b with hst₂
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₂ hM₂ => ?_
  have hst : st₂ = if (!isLeft) = true then st₁.setRight pa b else st₁.setLeft pa b := by
    rcases Bool.eq_false_or_eq_true isLeft with h | h <;> simp [st₂, h]
  have hN₂ : Lay.NodesAt M₂ nb cap st₂ := by
    rw [hM₂]; dsimp only; rw [h1il, hst]; exact hN₁.setSide Lay hpc (!isLeft)
  have hF₂ : TreeFrame Lay nb cap heap mem M₂ := by
    rw [hM₂]; dsimp only; exact hF₁.trans (TreeFrame.of_ctrl hpc (by omega) hApa hF₁.1)
  -- st3: the parent of `b` becomes `p`
  set st₃ := if b = 0 then st₂ else st₂.setPar b pa with hst₃
  refine runs_seq_condStore_named_le (by eval_expr) (fun _ => by eval_expr) (fun _ => by eval_expr)
    fun M₃ hM₃ => ?_
  have hNF₃ : Lay.NodesAt M₃ nb cap st₃ ∧ TreeFrame Lay nb cap heap mem M₃ := by
    by_cases hb0 : b = 0
    · have e1 : st₃ = st₂ := if_pos hb0
      have e2 : M₃ = M₂ := by rw [hM₃]; exact if_pos hb0
      rw [e1, e2]; exact ⟨hN₂, hF₂⟩
    · have e1 : st₃ = st₂.setPar b pa := if_neg hb0
      have e2 : M₃ = Function.update M₂ (Lay.nodeAddr nb b + NodeLayout.OFF_PAR) pa := by
        rw [hM₃]; exact if_neg hb0
      rw [e1, e2]
      exact ⟨hN₂.setPar Lay hbc, hF₂.trans (TreeFrame.of_ctrl hbc (by decide) hAb hF₂.1)⟩
  obtain ⟨hN₃, hF₃⟩ := hNF₃
  -- st4 .. st7
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₄ hM₄ => ?_
  have hN₄ : Lay.NodesAt M₄ nb cap (st₃.setPar pa x) := by
    rw [hM₄]; dsimp only; exact hN₃.setPar Lay hpc
  have hF₄ : TreeFrame Lay nb cap heap mem M₄ := by
    rw [hM₄]; dsimp only; exact hF₃.trans (TreeFrame.of_ctrl hpc (by decide) hApa hF₃.1)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₅ hM₅ => ?_
  have hN₅ : Lay.NodesAt M₅ nb cap ((st₃.setPar pa x).setPar x g) := by
    rw [hM₅]; dsimp only; exact hN₄.setPar Lay hx
  have hF₅ : TreeFrame Lay nb cap heap mem M₅ := by
    rw [hM₅]; dsimp only; exact hF₄.trans (TreeFrame.of_ctrl hx (by decide) hAx hF₄.1)
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₆ hM₆ => ?_
  have hN₆ : Lay.NodesAt M₆ nb cap (((st₃.setPar pa x).setPar x g).setPpar x pp) := by
    rw [hM₆]; dsimp only; exact hN₅.setPpar Lay hx
  have hF₆ : TreeFrame Lay nb cap heap mem M₆ := by
    rw [hM₆]; dsimp only; exact hF₅.trans (TreeFrame.of_ctrl hx (by decide) hAx hF₅.1)
  set st₇ := (((st₃.setPar pa x).setPar x g).setPpar x pp).setPpar pa 0 with hst₇
  refine runs_seq_store_named_le (by eval_expr) (by eval_expr) fun M₇ hM₇ => ?_
  have hN₇ : Lay.NodesAt M₇ nb cap st₇ := by
    rw [hM₇]; dsimp only; exact hN₆.setPpar Lay hpc
  have hF₇ : TreeFrame Lay nb cap heap mem M₇ := by
    rw [hM₇]; dsimp only; exact hF₆.trans (TreeFrame.of_ctrl hpc (by decide) hApa hF₆.1)
  -- st8: the child pointer of `g` that held `p` now holds `x`
  wram_step; try dsimp only
  have hmG : M₇ (nb + Lay.nodeStride * g) = (st₇.nodes g).left := (hN₇ g hgc).1
  wram_step; try dsimp only
  rw [hmG]
  set isP := (pa == (st₇.nodes g).left) with hisP
  have hil₂ : (if pa = (st₇.nodes g).left then 1 else 0) = (if isP then 1 else 0) := by
    simp [isP]
  rw [hil₂]
  have hil₂1 : (if isP then 1 else 0) ≤ 1 := by split_ifs <;> omega
  have h1il₂ : 1 - (if isP then 1 else 0) = (if (!isP) = true then 1 else 0) := by
    rcases Bool.eq_false_or_eq_true isP with h | h <;> simp [h]
  generalize hil₂_eq : (if isP then 1 else 0) = il₂ at hil₂1 h1il₂ ⊢
  set st₈ := if g = 0 then st₇ else if isP then st₇.setLeft g x else st₇.setRight g x with hst₈
  refine runs_seq_condStore_named_le (by eval_expr) (fun _ => by eval_expr) (fun _ => by eval_expr)
    fun M₈ hM₈ => ?_
  have hNF₈ : Lay.NodesAt M₈ nb cap st₈ ∧ TreeFrame Lay nb cap heap mem M₈ := by
    by_cases hg0 : g = 0
    · have e1 : st₈ = st₇ := if_pos hg0
      have e2 : M₈ = M₇ := by rw [hM₈]; exact if_pos hg0
      rw [e1, e2]; exact ⟨hN₇, hF₇⟩
    · have hst : (if isP then st₇.setLeft g x else st₇.setRight g x) =
          if (!isP) = true then st₇.setRight g x else st₇.setLeft g x := by
        rcases Bool.eq_false_or_eq_true isP with h | h <;> simp [h]
      have e1 : st₈ = if (!isP) = true then st₇.setRight g x else st₇.setLeft g x := by
        rw [← hst]; exact if_neg hg0
      have e2 : M₈ = Function.update M₇ (Lay.nodeAddr nb g + if (!isP) = true then 1 else 0) x := by
        rw [hM₈, ← h1il₂]; exact if_neg hg0
      rw [e1, e2]
      exact ⟨hN₇.setSide Lay hgc (!isP), hF₇.trans (TreeFrame.of_ctrl hgc
        (by split_ifs <;> decide) hAg hF₇.1)⟩
  obtain ⟨hN₈, hF₈⟩ := hNF₈
  have hmid : st₈ = rotateMid st x := by subst hb_eq; rfl
  rw [hmid] at hN₈
  obtain ⟨okp, okx⟩ := hok hx0 hp0
  -- the two pulls
  refine runs_seq_callBody_le hpull (by eval_expr)
    (R := fun _ st₉ c₉ => Lay.NodesAt st₉.mem nb cap (SplayState.pull P (rotateMid st x) pa) ∧
      TreeFrame Lay nb cap heap mem st₉.mem ∧ c₉ ≤ S.cost + 150) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := pullBody_runs S ω hN₈ (hptr.rotateMid hx) hpc
      ⟨hrec, hroom, hF₈.1, hwide⟩ (fun _ => okp)
    exact ⟨o, st', c, hr, hn, hF₈.trans hf, by omega⟩
  rintro - st₉ c₉ ⟨hN₉, hF₉, hc₉⟩
  refine runs_seq_callBody_le hpull (by eval_expr)
    (R := fun _ st₁₀ c₁₀ => Lay.NodesAt st₁₀.mem nb cap (SplayState.rotate P st x) ∧
      TreeFrame Lay nb cap heap mem st₁₀.mem ∧ c₁₀ ≤ S.cost + 150) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := pullBody_runs S ω hN₉
      ((hptr.rotateMid hx).pull hpc) hx ⟨hrec, hroom, hF₉.1, hwide⟩ (fun _ => okx)
    refine ⟨o, st', c, hr, ?_, hF₉.trans hf, by omega⟩
    rw [rotate_eq hx0 hp0]; exact hn
  rintro - st₁₀ c₁₀ ⟨hN₁₀, hF₁₀, hc₁₀⟩
  wram_step
  · exact ⟨hN₁₀, hF₁₀⟩
  · simp only [rotateCost]; wram_cost

end MinCostFlow.LinkCut.Gen
