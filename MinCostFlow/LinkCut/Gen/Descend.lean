module

public import MinCostFlow.LinkCut.Gen.Walk
public import MinCostFlow.LinkCut.PathTree.Descend

/-!
# The descent as a program

`descendBody` is the machine version of `PathTree.descend`. Like `leftmostWalkBody`, it is
recursive with the fuel as an argument. At each node it calls `pushDown`, then asks the payload
whether the summary of the left child is ready (`sumTest`) and, if it is not, whether the node's
own value is ready (`valTest`). The two tests only read memory (`sumTestContract`,
`valTestContract`); the payload supplies them (`ReadyTests`).

`descendSteps` counts the nodes the model visits, and the cost is at most `descendSteps + 1`
times the cost of one visit.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Gen

open WordRAM MinCostFlow.LinkCut.Prog NodeLayout MinCostFlow.LinkCut.PathTree

variable {α σ τ : Type*}

/-- `sumTest [a]`: return `1` if the summary of the record at `a` is ready, else `0`. Memory is
unchanged. The test gets the record, not the summary block, so that it can read the layout words
of the value block. -/
def sumTestContract (Lay : NodeLayout α σ τ) (rs : σ → Bool) (w cost : ℕ) : Contract where
  pre args mem := ∃ a v s, args = [a] ∧ a + Lay.nodeStride < 2 ^ w ∧
    Lay.ValAt mem (a + OFF_VAL) v ∧ Lay.SumAt mem (a + Lay.offSum) s
  post args mem v mem' := mem' = mem ∧
    ∀ s, Lay.SumAt mem (args.getD 0 0 + Lay.offSum) s → v = if rs s then 1 else 0
  cost _ _ := cost

/-- `valTest [a]`: return `1` if the value at `a` is ready, else `0`. Memory is unchanged. -/
def valTestContract (Lay : NodeLayout α σ τ) (rv : α → Bool) (w cost : ℕ) : Contract where
  pre args mem := ∃ a v, args = [a] ∧ a + Lay.valW < 2 ^ w ∧ Lay.ValAt mem a v
  post args mem r mem' := mem' = mem ∧
    ∀ v, Lay.ValAt mem (args.getD 0 0) v → r = if rv v then 1 else 0
  cost _ _ := cost

/-- The two readiness tests of a payload, at their indices in `p`. -/
structure ReadyTests (w : ℕ) (p : Program) (Lay : NodeLayout α σ τ) (rs : σ → Bool)
    (rv : α → Bool) where
  sumTest : ℕ
  valTest : ℕ
  cost : ℕ
  sum_ok : MeetsContract w p sumTest (sumTestContract Lay rs w cost)
  val_ok : MeetsContract w p valTest (valTestContract Lay rv w cost)

/-- The payload values that `descend P rs rv st fuel x` computes are representable. -/
def DescendOk (ok : PayloadOk α σ τ) (P : LctPayload α σ τ) (rs : σ → Bool) (rv : α → Bool) :
    SplayState α σ τ → ℕ → ℕ → Prop
  | _, 0, _ => True
  | st, k + 1, x =>
    let s1 := SplayState.pushDown P st x
    let l := (s1.nodes x).left
    PushDownOk ok P st x ∧
      (if l ≠ 0 ∧ rs (s1.nodes l).sum = true then DescendOk ok P rs rv s1 k l
       else if rv (s1.nodes x).val = true then True
       else DescendOk ok P rs rv s1 k (s1.nodes x).right)

theorem descend_ptr {cap : ℕ} {P : LctPayload α σ τ} {rs : σ → Bool} {rv : α → Bool} :
    ∀ (k x : ℕ) {st : SplayState α σ τ}, PtrOk cap st → x ≤ cap →
      PtrOk cap (descend P rs rv st k x).1 ∧ (descend P rs rv st k x).2 ≤ cap
  | 0, x, _, h, hx => ⟨h, hx⟩
  | k + 1, x, st, h, hx => by
    unfold descend
    dsimp only
    have h1 := h.pushDown (P := P) hx
    split_ifs with hl hv
    · exact descend_ptr k _ h1 (h1 x hx).1
    · exact ⟨h1, hx⟩
    · exact descend_ptr k _ h1 (h1 x hx).2.1

/-- `descend` on `[nb, x, fuel, heap]`; returns the node it stops at. `selfProc` is this
procedure. -/
def descendBody (selfProc pdProc sumProc valProc : ℕ) : Stmt :=
  strideLoad ;;
  .cond (.bin .eq (.reg 2) (.const 0)) (.ret (.reg 1))
    (.call 4 pdProc [.reg 0, .reg 1, .reg 3] ;;
     .assign 5 (.load (recAddr 1)) ;;
     .call 6 sumProc [recAddr 5] ;;
     .cond (.bin .mul (.bin .lt (.const 0) (.reg 5)) (.reg 6))
       (.call 7 selfProc [.reg 0, .reg 5, .bin .sub (.reg 2) (.const 1), .reg 3] ;;
        .ret (.reg 7))
       (.call 7 valProc [.bin .add (recAddr 1) (.const OFF_VAL)] ;;
        .cond (.reg 7) (.ret (.reg 1))
          (.call 8 selfProc [.reg 0, .load (.bin .add (recAddr 1) (.const 1)),
              .bin .sub (.reg 2) (.const 1), .reg 3] ;;
           .ret (.reg 8))))

theorem descendBody_noRand (selfProc pdProc sumProc valProc : ℕ) :
    (descendBody selfProc pdProc sumProc valProc).NoRand := by
  simp [descendBody, recAddr, Stmt.NoRand]

/-- The run of `descendBody`. -/
theorem descendBody_runs {w nb cap heap dp : ℕ} {P : LctPayload α σ τ}
    {Lay : NodeLayout α σ τ} {ok : PayloadOk α σ τ} {p : Program} {rs : σ → Bool}
    {rv : α → Bool} {S : PayloadSteps w p P Lay ok} (L : LazyProcs w p P Lay ok S)
    (T : ReadyTests w p Lay rs rv)
    (hself : p.procs[dp]? = some (descendBody dp L.pushDown T.sumTest T.valTest))
    (ω : ℕ → Bool) :
    ∀ (k x pos : ℕ) {mem : ℕ → ℕ} {st : SplayState α σ τ},
    Lay.NodesAt mem nb cap st → PtrOk cap st → x ≤ cap →
    HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) mem → k < 2 ^ w →
    DescendOk ok P rs rv st k x →
    ∃ o st' c, Runs w p ω (descendBody dp L.pushDown T.sumTest T.valTest)
        (startState [nb, x, k, heap] mem pos) o st' c ∧
      (o.value = (descend P rs rv st k x).2 ∧
        Lay.NodesAt st'.mem nb cap (descend P rs rv st k x).1 ∧
        TreeFrame Lay nb cap heap mem st'.mem) ∧
      0 + c ≤ (descendSteps P rs rv st k x + 1) * (pushDownCost S + 2 * T.cost + 120)
  | 0, x, pos, mem, st, hnodes, hptr, hx, hheap, hk, hok => by
    have hwide := hheap.wide
    unfold descendBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step
    · wram_step
      · exact ⟨by simp [descend, Outcome.value], by simpa [descend] using hnodes,
          TreeFrame.refl hheap.zero⟩
      · simp only [descendSteps, pushDownCost]; wram_cost
  | k + 1, x, pos, mem, st, hnodes, hptr, hx, hheap, hk, hok => by
    have hroom := hheap.room
    have hwide := hheap.wide
    have hS := hheap.stride_lt
    have hS6 := Lay.stride_pos
    have hA := hheap.addr_lt hx
    have hxS : x ≤ Lay.nodeStride * x := Nat.le_mul_of_pos_left x (by omega)
    set C := pushDownCost S + 2 * T.cost + 120 with hC
    have hT := Nat.le_mul_of_pos_left C (by omega : 0 < descendSteps P rs rv st (k + 1) x + 1)
    unfold nodeAddr at hA
    unfold descendBody
    rw [startState]
    refine runs_seq_strideLoad_le (by simp) hnodes.stride hheap.nb6 ?_
    wram_step
    obtain ⟨okD, okR⟩ := hok
    set st₁ := SplayState.pushDown P st x with hst₁
    refine runs_seq_callBody_le L.pushDown_body (by eval_expr)
      (R := fun _ m₁ c₁ => Lay.NodesAt m₁.mem nb cap st₁ ∧
        TreeFrame Lay nb cap heap mem m₁.mem ∧ c₁ ≤ pushDownCost S) ?_ ?_
    · obtain ⟨o, st', c, hr, ⟨hn, hf⟩, hc⟩ := pushDownBody_runs L ω hnodes hptr hx hheap okD
      exact ⟨o, st', c, hr, hn, hf, by omega⟩
    rintro - m₁ c₁ ⟨hn₁, hf₁, hc₁⟩
    have hp₁ : PtrOk cap st₁ := hptr.pushDown hx
    have hlc := (hp₁ x hx).1
    have hrc := (hp₁ x hx).2.1
    set l := (st₁.nodes x).left with hl
    set r := (st₁.nodes x).right with hr
    obtain ⟨hm0, hm1, -, -, -, -, hvx, -, -⟩ := hn₁ x hx
    obtain ⟨-, -, -, -, -, -, hvl, hsl, -⟩ := hn₁ l hlc
    have hAl := hheap.addr_lt hlc
    unfold nodeAddr at hAl hm0 hm1 hvx hsl hvl
    simp only [NodeLayout.OFF_LEFT, Nat.add_zero] at hm0
    simp only [NodeLayout.OFF_RIGHT] at hm1
    have hlS : l ≤ Lay.nodeStride * l := Nat.le_mul_of_pos_left l (by omega)
    have hAl' : nb + Lay.nodeStride * (st₁.nodes x).left + Lay.nodeStride ≤ heap := hAl
    have hoffS : Lay.offSum + Lay.sumW ≤ Lay.nodeStride := by unfold offSum nodeStride; omega
    have hoffV : OFF_VAL + Lay.valW ≤ Lay.nodeStride := by unfold OFF_VAL nodeStride; omega
    wram_step; try dsimp only
    rw [hm0]
    have hsum_ok := T.sum_ok
    wram_step
    all_goals try (simp only [← hl]; omega)
    all_goals try (intro v hv; simp only [List.mem_singleton] at hv; subst hv; simp only [← hl]; omega)
    · exact ⟨_, _, _, rfl, by omega, hvl, hsl⟩
    rintro v₁ mem₁ pos₁ ⟨hmem₁, hres₁⟩
    subst hmem₁
    have hv₁ : v₁ = if rs (st₁.nodes l).sum then 1 else 0 := hres₁ _ hsl
    subst hv₁
    have hrec_l : (st₁.nodes x).left = l := rfl
    -- the case split of the model
    have hmodel : descend P rs rv st (k + 1) x =
        if l ≠ 0 ∧ rs (st₁.nodes l).sum = true then descend P rs rv st₁ k l
        else if rv (st₁.nodes x).val = true then (st₁, x)
        else descend P rs rv st₁ k r := rfl
    have hsteps : descendSteps P rs rv st (k + 1) x =
        if l ≠ 0 ∧ rs (st₁.nodes l).sum = true then 1 + descendSteps P rs rv st₁ k l
        else if rv (st₁.nodes x).val = true then 1
        else 1 + descendSteps P rs rv st₁ k r := rfl
    have hokR : (if l ≠ 0 ∧ rs (st₁.nodes l).sum = true then DescendOk ok P rs rv st₁ k l
        else if rv (st₁.nodes x).val = true then True
        else DescendOk ok P rs rv st₁ k r) := okR
    have hheap₁ : HeapOk Lay w nb cap heap (2 * Lay.tagW + S.space) m₁.mem :=
      ⟨hheap.rec_le, hroom, hf₁.1, hwide⟩
    refine runs_cond_le (by eval_expr; split_ifs <;> omega) ?_ ?_
    · -- go left
      intro hgo
      have hgl : l ≠ 0 ∧ rs (st₁.nodes l).sum = true := by
        by_cases h0 : l = 0
        · simp [h0] at hgo
        · refine ⟨h0, ?_⟩
          by_contra h; simp [h] at hgo
      rw [if_pos hgl] at hmodel hsteps hokR
      refine runs_seq_callBody_le hself (by eval_expr)
        (R := fun v m₂ c₂ => v = (descend P rs rv st₁ k l).2 ∧
          Lay.NodesAt m₂.mem nb cap (descend P rs rv st₁ k l).1 ∧
          TreeFrame Lay nb cap heap mem m₂.mem ∧
          c₂ ≤ (descendSteps P rs rv st₁ k l + 1) * C) ?_ ?_
      · obtain ⟨o, st', c, hr', ⟨hv, hn, hf⟩, hc⟩ := descendBody_runs L T hself ω k l _ hn₁ hp₁
          hlc hheap₁ (by omega) hokR
        simp only [← hC] at hc
        exact ⟨o, st', c, by simpa using hr', hv, hn, hf₁.trans hf, by omega⟩
      rintro v₂ m₂ c₂ ⟨hv₂, hn₂, hf₂, hc₂⟩
      wram_step
      · refine ⟨?_, ?_, hf₂⟩
        · simp [Outcome.value, hmodel, hv₂]
        · rw [hmodel]; exact hn₂
      · rw [hsteps] at hT ⊢
        have : (1 + descendSteps P rs rv st₁ k l + 1) * C =
            (descendSteps P rs rv st₁ k l + 1) * C + C := by ring
        rw [this]
        simp only [sumTestContract, valTestContract, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
          argsSize_cons, argsSize_nil] at *
        omega
    · intro hgo
      have hgl : ¬ (l ≠ 0 ∧ rs (st₁.nodes l).sum = true) := by
        rintro ⟨h0, h1⟩
        simp [h1] at hgo
        omega
      rw [if_neg hgl] at hmodel hsteps hokR
      have hval_ok := T.val_ok
      wram_step
      all_goals try (simp only [← hl]; omega)
      all_goals try (intro v hv; simp only [List.mem_singleton] at hv; subst hv; omega)
      · exact ⟨_, _, rfl, by omega, hvx⟩
      rintro v₃ mem₃ pos₃ ⟨hmem₃, hres₃⟩
      subst hmem₃
      have hv₃ : v₃ = if rv (st₁.nodes x).val then 1 else 0 := hres₃ _ hvx
      subst hv₃
      by_cases hrv : rv (st₁.nodes x).val = true
      · rw [if_pos hrv] at hmodel hsteps
        refine runs_cond_le (Expr.eval_reg_of_eq (by simp [hrv]; rfl)) ?_ ?_
        · intro _
          wram_step
          · refine ⟨?_, ?_, hf₁⟩
            · simp [Outcome.value, hmodel]
            · rw [hmodel]; exact hn₁
          · rw [hsteps] at hT ⊢
            simp only [sumTestContract, valTestContract, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
              argsSize_cons, argsSize_nil] at *
            omega
        · intro h; simp [hrv] at h
      · rw [if_neg hrv] at hmodel hsteps hokR
        refine runs_cond_le (Expr.eval_reg_of_eq (by simp [hrv]; rfl)) ?_ ?_
        · intro h; simp [hrv] at h
        intro _
        refine runs_seq_callBody_le hself (by eval_expr)
          (R := fun v m₂ c₂ => v = (descend P rs rv st₁ k r).2 ∧
            Lay.NodesAt m₂.mem nb cap (descend P rs rv st₁ k r).1 ∧
            TreeFrame Lay nb cap heap mem m₂.mem ∧
            c₂ ≤ (descendSteps P rs rv st₁ k r + 1) * C) ?_ ?_
        · obtain ⟨o, st', c, hr', ⟨hv, hn, hf⟩, hc⟩ := descendBody_runs L T hself ω k r _ hn₁ hp₁
            hrc hheap₁ (by omega) hokR
          simp only [← hC] at hc
          refine ⟨o, st', c, ?_, hv, hn, hf₁.trans hf, by omega⟩
          rw [hm1]; simpa using hr'
        rintro v₂ m₂ c₂ ⟨hv₂, hn₂, hf₂, hc₂⟩
        wram_step
        · refine ⟨?_, ?_, hf₂⟩
          · simp [Outcome.value, hmodel, hv₂]
          · rw [hmodel]; exact hn₂
        · rw [hsteps] at hT ⊢
          have : (1 + descendSteps P rs rv st₁ k r + 1) * C =
              (descendSteps P rs rv st₁ k r + 1) * C + C := by ring
          rw [this]
          simp only [sumTestContract, valTestContract, Expr.size_bin, Expr.size_reg, Expr.size_const, Expr.size_load,
            argsSize_cons, argsSize_nil] at *
          omega

end MinCostFlow.LinkCut.Gen
