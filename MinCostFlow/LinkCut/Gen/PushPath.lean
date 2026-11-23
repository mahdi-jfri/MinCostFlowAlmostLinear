module

public import MinCostFlow.LinkCut.Gen.PushDownTag
public import MinCostFlow.LinkCut.ForestExposeOps

/-!
# `pushDown` and `pushPath` as programs

`pushDownBody` calls `pushDownRev` and then `pushDownTag` on node `x`, as
`SplayState.pushDown` does. `pushPathBody` is the machine version of `SplayState.pushPath`: a
recursive procedure with the fuel as an argument, which first pushes along the path of the
parent and then pushes down at `x`. Its cost is at most `splayDepth st fuel x + 1` times the
cost of one `pushDown` call plus a constant (`pushPathBody_runs`).

The first part of the file shows that the lazy operations keep `PtrOk`.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout

variable {α σ τ : Type*}

/-! ### The lazy operations keep `PtrOk` -/

theorem PtrOk.updateNode_ptrs {cap x : ℕ} {st : SplayState α σ τ}
    {f : SplayNode α σ τ → SplayNode α σ τ} (h : PtrOk cap st)
    (hf : (f (st.nodes x)).left ≤ cap ∧ (f (st.nodes x)).right ≤ cap ∧
      (f (st.nodes x)).par ≤ cap ∧ (f (st.nodes x)).ppar ≤ cap) :
    PtrOk cap (st.updateNode x f) := fun y hy => by
  by_cases hyx : y = x
  · subst hyx; simpa using hf
  · simpa [hyx] using h y hy

theorem PtrOk.revNode {cap x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.revNode P st x) := by
  unfold SplayState.revNode
  split_ifs
  · exact h
  · obtain ⟨h1, h2, h3, h4⟩ := h x hx
    exact h.updateNode_ptrs ⟨h2, h1, h3, h4⟩

theorem PtrOk.applyTagNode {cap x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ} {t : τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.applyTagNode P st x t) := by
  unfold SplayState.applyTagNode
  split_ifs
  · exact h
  · exact h.updateNode_ptrs (by simpa using h x hx)

theorem PtrOk.pull {cap x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.pull P st x) := by
  unfold SplayState.pull
  by_cases hx0 : x = 0
  · rw [if_pos hx0]; exact h
  · rw [if_neg hx0]; exact h.updateNode_ptrs (by simpa using h x hx)

theorem PtrOk.pushDownRev {cap x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.pushDownRev P st x) := by
  unfold SplayState.pushDownRev
  dsimp only
  split_ifs
  · exact h
  · obtain ⟨h1, h2, h3, h4⟩ := h x hx
    exact ((h.updateNode_ptrs (by simpa using h x hx)).revNode h1).revNode h2
  · exact h

theorem PtrOk.pushDownTag {cap x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.pushDownTag P st x) := by
  unfold SplayState.pushDownTag
  dsimp only
  split_ifs
  · exact h
  · exact h
  · obtain ⟨h1, h2, h3, h4⟩ := h x hx
    exact ((h.updateNode_ptrs (by simpa using h x hx)).applyTagNode h1).applyTagNode h2

theorem PtrOk.pushDown {cap x : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) (hx : x ≤ cap) : PtrOk cap (SplayState.pushDown P st x) :=
  (h.pushDownRev hx).pushDownTag hx

theorem PtrOk.pushPath {cap : ℕ} {P : LctPayload α σ τ} {st : SplayState α σ τ}
    (h : PtrOk cap st) : ∀ (k x : ℕ), x ≤ cap → PtrOk cap (SplayState.pushPath P st k x)
  | 0, _, _ => h
  | k + 1, x, hx => by
    unfold SplayState.pushPath
    dsimp only
    split_ifs with h0 hp
    · exact h
    · exact h.pushDown hx
    · exact (PtrOk.pushPath h k _ (h x hx).2.2.1).pushDown hx

/-! ### `pushDown` -/

/-- `pushDown` on `[nb, x, heap]`. -/
def pushDownBody (pdrProc pdtProc : ℕ) : Stmt :=
  .call 3 pdrProc [.reg 0, .reg 1, .reg 2] ;;
  .call 3 pdtProc [.reg 0, .reg 1, .reg 2] ;;
  .ret (.const 0)

theorem pushDownBody_noRand (pdrProc pdtProc : ℕ) : (pushDownBody pdrProc pdtProc).NoRand := by
  simp [pushDownBody, Stmt.NoRand]

/-- The payload values that `pushDown P st x` computes are representable. -/
def PushDownOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : SplayState α σ τ)
    (x : ℕ) : Prop :=
  PushDownRevOk ok P st x ∧ PushDownTagOk ok P (SplayState.pushDownRev P st x) x

/-- A bound on the cost of one `pushDown` call. -/
def pushDownCost {w : ℕ} {p : Program} {P : LctPayload α σ τ} {Lay : NodeLayout α σ τ}
    {ok : PayloadOk α σ τ} (S : PayloadSteps w p P Lay ok) : ℕ :=
  7 * S.cost + 40 * Lay.tagW + 600

/-- The procedures that the lazy tree programs call, at their indices in `p`. -/
structure LazyProcs (w : ℕ) (p : Program) (P : LctPayload α σ τ) (Lay : NodeLayout α σ τ)
    (ok : PayloadOk α σ τ) (S : PayloadSteps w p P Lay ok) where
  copy : ℕ
  revNode : ℕ
  applyTag : ℕ
  pushDownRev : ℕ
  pushDownTag : ℕ
  pushDown : ℕ
  copy_ok : MeetsContract w p copy (copyWordsContract w)
  revNode_body : p.procs[revNode]? = some (revNodeBody S.rev)
  applyTag_body : p.procs[applyTag]? = some (applyTagBody S.act)
  pushDownRev_body : p.procs[pushDownRev]? = some (pushDownRevBody revNode)
  pushDownTag_body :
    p.procs[pushDownTag]? = some (pushDownTagBody S.isId S.setId copy applyTag)
  pushDown_body : p.procs[pushDown]? = some (pushDownBody pushDownRev pushDownTag)

/-- The run of `pushDownBody`. -/
theorem pushDownBody_runs {w nb cap x heap pos : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    {S : PayloadSteps w p P Lay ok} (L : LazyProcs w p P Lay ok S)
    (ω : ℕ → Bool) {mem : ℕ → ℕ} {st : SplayState α σ τ}
    (hnodes : Lay.NodesAt mem nb cap st) (hptr : PtrOk cap st) (hx : x ≤ cap)
    (hheap : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem)
    (hok : PushDownOk ok P st x) :
    ∃ o st' c, Runs w p ω (pushDownBody L.pushDownRev L.pushDownTag)
        (startState [nb, x, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.pushDown P st x) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧ 0 + c ≤ pushDownCost S := by
  have hwide := hheap.wide
  unfold pushDownBody
  rw [startState]
  refine runs_seq_callBody_le L.pushDownRev_body (by eval_expr)
    (R := fun _ st₁ c₁ => Lay.NodesAt st₁.mem nb cap (SplayState.pushDownRev P st x) ∧
      TreeFrame Lay nb cap heap mem st₁.mem ∧ c₁ ≤ 2 * S.cost + 200) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := pushDownRevBody_runs S L.revNode_body ω hnodes hptr
      hx (hheap.mono (by omega)) hok.1
    exact ⟨o, st', c, hr, hn, hf, by omega⟩
  rintro - st₁ c₁ ⟨hn₁, hf₁, hc₁⟩
  refine runs_seq_callBody_le L.pushDownTag_body (by eval_expr)
    (R := fun _ st₂ c₂ => Lay.NodesAt st₂.mem nb cap (SplayState.pushDown P st x) ∧
      TreeFrame Lay nb cap heap mem st₂.mem ∧ c₂ ≤ 5 * S.cost + 40 * Lay.tagW + 300) ?_ ?_
  · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := pushDownTagBody_runs S L.copy_ok L.applyTag_body ω
      hn₁ (hptr.pushDownRev hx) hx ⟨hheap.rec_le, hheap.room, hf₁.1, hwide⟩ hok.2
    exact ⟨o, st', c, hr, hn, hf₁.trans hf, by omega⟩
  rintro - st₂ c₂ ⟨hn₂, hf₂, hc₂⟩
  wram_step
  · exact ⟨hn₂, hf₂⟩
  · unfold pushDownCost; wram_cost

/-! ### `pushPath` -/

/-- `pushPath` on `[nb, x, fuel, heap]`; procedure `selfProc` is this procedure. -/
def pushPathBody (selfProc pdProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.const 0))
    (.cond (.bin .eq (.reg 1) (.const 0)) (.ret (.const 0))
      (.assign 4 (.load (.bin .add (recAddr 1) (.const 2))) ;;
       .cond (.reg 4) (.call 5 selfProc [.reg 0, .reg 4, .bin .sub (.reg 2) (.const 1), .reg 3])
         .nop ;;
       .call 5 pdProc [.reg 0, .reg 1, .reg 3] ;;
       .ret (.const 0)))

theorem pushPathBody_noRand (selfProc pdProc : ℕ) :
    (pushPathBody selfProc pdProc).NoRand := by
  simp [pushPathBody, recAddr, Stmt.NoRand]

/-- The payload values that `pushPath P st fuel x` computes are representable. -/
def PushPathOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (st : SplayState α σ τ) :
    ℕ → ℕ → Prop
  | 0, _ => True
  | k + 1, x => x ≠ 0 →
      ((st.nodes x).par ≠ 0 → PushPathOk ok P st k (st.nodes x).par) ∧
      PushDownOk ok P
        (if (st.nodes x).par = 0 then st else SplayState.pushPath P st k (st.nodes x).par) x

/-- The run of `pushPathBody`. -/
theorem pushPathBody_runs {w nb cap heap pp : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program}
    {S : PayloadSteps w p P Lay ok} (L : LazyProcs w p P Lay ok S)
    (hself : p.procs[pp]? = some (pushPathBody pp L.pushDown)) (ω : ℕ → Bool) :
    ∀ (k x pos : ℕ) {mem : ℕ → ℕ} {st : SplayState α σ τ},
    Lay.NodesAt mem nb cap st → PtrOk cap st → x ≤ cap →
    HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem → k < 2 ^ w →
    PushPathOk ok P st k x →
    ∃ o st' c, Runs w p ω (pushPathBody pp L.pushDown)
        (startState [nb, x, k, heap] mem pos) o st' c ∧
      (Lay.NodesAt st'.mem nb cap (SplayState.pushPath P st k x) ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧
      0 + c ≤ (splayDepth st k x + 1) * (pushDownCost S + 80)
  | 0, x, pos, mem, st, hnodes, hptr, hx, hheap, hk, hok => by
    have hwide := hheap.wide
    unfold pushPathBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step
    · wram_step
      · exact ⟨by simpa [SplayState.pushPath] using hnodes, TreeFrame.refl hheap.zero⟩
      · simp only [splayDepth, pushDownCost]; wram_cost
  | k + 1, x, pos, mem, st, hnodes, hptr, hx, hheap, hk, hok => by
    have hroom := hheap.room
    have hwide := hheap.wide
    have hS := hheap.stride_lt
    have hS6 := Lay.stride_pos
    have hA := hheap.addr_lt hx
    have hxS : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
    obtain ⟨-, -, hpq, -⟩ := hptr x hx
    obtain ⟨-, -, h2, -, -, -, -, -, -⟩ := hnodes x hx
    have hm2 : mem (nb + Lay.nodeStride * x + 2) = (st.nodes x).par := h2
    set q := (st.nodes x).par with hq_def
    set C := pushDownCost S with hC
    unfold nodeAddr at hA
    -- the last part: `pushDown` at `x` and return
    have fin : x ≠ 0 → ∀ (st₁ : State) (s₁ : SplayState α σ τ), st₁.regs 0 = nb → st₁.regs 1 = x →
        st₁.regs 3 = heap → Lay.NodesAt st₁.mem nb cap s₁ → PtrOk cap s₁ →
        TreeFrame Lay nb cap heap mem st₁.mem → PushDownOk ok P s₁ x →
        s₁ = (if q = 0 then st else SplayState.pushPath P st k q) → ∀ k₀ T, k₀ + C + 10 ≤ T →
        ∃ o st' c, Runs w p ω (.seq (.call 5 L.pushDown [.reg 0, .reg 1, .reg 3])
            (.ret (.const 0))) st₁ o st' c ∧
          (Lay.NodesAt st'.mem nb cap (SplayState.pushPath P st (k + 1) x) ∧
            TreeFrame Lay nb cap heap mem st'.mem) ∧ k₀ + c ≤ T := by
      intro hx0 st₁ s₁ r0 r1 r3 hn₁ hp₁ hf₁ hok₁ hs₁ k₀ T hkT
      refine runs_seq_callBody_le L.pushDown_body (by eval_expr)
        (R := fun _ st₂ c₂ => Lay.NodesAt st₂.mem nb cap (SplayState.pushDown P s₁ x) ∧
          TreeFrame Lay nb cap heap mem st₂.mem ∧ c₂ ≤ C) ?_ ?_
      · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := pushDownBody_runs L ω hn₁ hp₁ hx
          ⟨hheap.rec_le, hroom, hf₁.1, hwide⟩ hok₁
        exact ⟨o, st', c, hr, hn, hf₁.trans hf, by omega⟩
      rintro - st₂ c₂ ⟨hn₂, hf₂, hc₂⟩
      wram_step
      · refine ⟨?_, hf₂⟩
        have : SplayState.pushPath P st (k + 1) x = SplayState.pushDown P s₁ x := by
          rw [hs₁]; simp only [SplayState.pushPath, hx0, if_false]; rfl
        rw [this]; exact hn₂
      · wram_cost
    unfold pushPathBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step
    wram_step
    · subst hcond
      have hT := Nat.le_mul_of_pos_left (C + 80)
        (by omega : 0 < splayDepth st (k + 1) 0 + 1)
      wram_step
      · exact ⟨by simpa [SplayState.pushPath] using hnodes, TreeFrame.refl hheap.zero⟩
      · simp only [hC, pushDownCost] at *; wram_cost
    have hx0 : x ≠ 0 := hcond
    obtain ⟨hokq, hokd⟩ := hok hx0
    wram_step; try dsimp only
    rw [hm2]
    have hd : splayDepth st (k + 1) x = if q = 0 then 0 else 1 + splayDepth st k q := by
      simp [splayDepth, q]
    refine runs_seq_cond_le (Expr.eval_reg_of_eq (by simp; rfl)) ?_ ?_
    · intro hq0
      have hq0' : ¬ (st.nodes x).par = 0 := hq0
      have hqw : q < 2 ^ w := by
        have h₁ := hheap.addr_lt hpq; unfold nodeAddr at h₁
        have h₂ : q ≤ Lay.nodeStride * q := Nat.le_mul_of_pos_left q (by omega)
        omega
      refine runs_seq_callBody_le hself (by eval_expr)
        (R := fun _ st₁ c₁ => Lay.NodesAt st₁.mem nb cap (SplayState.pushPath P st k q) ∧
          TreeFrame Lay nb cap heap mem st₁.mem ∧ c₁ ≤ (splayDepth st k q + 1) * (C + 80)) ?_ ?_
      · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := pushPathBody_runs L hself ω k q _ hnodes hptr hpq
          hheap (by omega) (hokq hq0)
        refine ⟨o, st', c, ?_, hn, hf, by simp only [← hC] at hc; omega⟩
        simpa using hr
      rintro v₁ st₁ c₁ ⟨hn₁, hf₁, hc₁⟩
      let R : ℕ → ℕ := Function.update (Function.update (fun i ↦ [nb, x, k + 1, heap].getD i 0)
        20 Lay.nodeStride) 4 q
      let st₁' : State := { st₁ with regs := Function.update R 5 v₁ }
      refine fin hx0 st₁' (SplayState.pushPath P st k q) (by simp [st₁', R]) (by simp [st₁', R]) (by simp [st₁', R]) hn₁
        (hptr.pushPath k q hpq) hf₁ (by simpa [hq0'] using hokd) (by simp [hq0]) _ _ ?_
      rw [hd, if_neg hq0]
      have : (1 + splayDepth st k q + 1) * (C + 80) = (splayDepth st k q + 1) * (C + 80) +
          (C + 80) := by ring
      rw [this]
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load, recAddr_size,
        argsSize_cons, argsSize_nil] at *
      omega
    · intro hq0
      have hq0' : (st.nodes x).par = 0 := hq0
      have hT := Nat.le_mul_of_pos_left (C + 80) (by omega : 0 < splayDepth st (k + 1) x + 1)
      refine runs_seq_nop_le ?_
      refine fin hx0 _ st (by simp) (by simp) (by simp) hnodes hptr
        (TreeFrame.refl hheap.zero) (by simpa [hq0'] using hokd) (by simp [hq0]) _ _ ?_
      simp only [Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load, recAddr_size,
        argsSize_cons, argsSize_nil] at *
      omega

end MinCostFlow.LinkCut.Gen
