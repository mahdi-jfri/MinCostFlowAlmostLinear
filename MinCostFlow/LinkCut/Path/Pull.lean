module

public import MinCostFlow.LinkCut.Path.Seg

/-!
# The pull step of the path payload

`pathPullBody` writes into the summary of the record at `a` the summary of its path: the left
child's path, then the node's own edge, then the right child's path. It builds the result in
scratch memory at the heap pointer with three `segBody` calls, copies it into the record, and
clears the scratch. Building it outside the record first lets a child record be the record at
`a` itself, as the pull contract allows.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen

/-- The summary width `3 K + 1`, with `K` in register `15`. -/
abbrev kSumW : Expr := .bin .add (.bin .mul (.const 3) (.reg 15)) (.const 1)

/-- `pull [x, a, l, r, heap]` for the path payload. -/
def pathPullBody (segProc copyProc : ℕ) : Stmt :=
  .assign 15 (.load (.bin .add (.reg 1) (.const 9))) ;;
  .assign 5 (.bin .add (.reg 4) kSumW) ;;
  .call 6 segProc [.reg 4, kAt 2 12 4, kAt 2 12 6, kAt 2 13 6, .reg 2, .reg 15, .reg 5] ;;
  .call 6 segProc [.reg 4, .bin .add (.reg 1) (.const 12), .bin .add (.reg 1) (.const 10),
    kAt 1 12 3, .load (.bin .add (.reg 1) (.const 10)), .reg 15, .reg 5] ;;
  .call 6 segProc [.reg 4, kAt 3 12 4, kAt 3 12 6, kAt 3 13 6, .reg 3, .reg 15, .reg 5] ;;
  .call 6 copyProc [.reg 4, kAt 1 12 4, kSumW] ;;
  .call 6 copyProc [.reg 5, .reg 4, kSumW] ;;
  .ret (.const 0)

theorem pathPullBody_noRand (a b : ℕ) : (pathPullBody a b).NoRand := by
  simp [pathPullBody, Stmt.NoRand]

/-- A child's summary as a segment. -/
theorem childSeg {mem : ℕ → ℕ} {h K c : ℕ} {s : PathSummary}
    (hc : ChildSumAt pathPayload (pathLayout h K) mem c s) :
    (c = 0 → s = PathSummary.empty) ∧
    (c ≠ 0 → SegAt mem (c + (12 + 4 * K)) (c + (12 + 6 * K)) (c + (13 + 6 * K)) h K s) := by
  rcases hc with ⟨hc0, hs⟩ | ⟨hc0, hs⟩
  · exact ⟨fun _ => hs, fun h' => absurd hc0 h'⟩
  · refine ⟨fun h' => absurd h' hc0, fun _ => ?_⟩
    change (pathLayout h K).SumAt mem (c + (pathLayout h K).offSum) s at hs
    rw [pathLayout_offSum] at hs
    obtain ⟨hg, hl, hd⟩ := pathSummaryAt_iff.mp (hs : PathSummaryAt mem _ h K s)
    rw [show c + (12 + 4 * K) + 2 * K = c + (12 + 6 * K) by omega] at hd
    rw [show c + (12 + 6 * K) + 1 = c + (13 + 6 * K) by omega] at hd
    exact ⟨hg, hl, hd⟩

/-- A node's own edge as a segment. -/
theorem valSeg {mem : ℕ → ℕ} {h K a : ℕ} {v : Option PathEdgeValue}
    (hv : PathEdgeAt mem (a + 10) h K v) :
    (mem (a + 10) = 0 → PathSummary.single v = PathSummary.empty) ∧
    (mem (a + 10) ≠ 0 → SegAt mem (a + 12) (a + 10) (a + (12 + 3 * K)) h K
      (PathSummary.single v)) := by
  cases v with
  | none => exact ⟨fun _ => rfl, fun h' => absurd hv h'⟩
  | some e =>
    obtain ⟨hh, -, hg, hl, -, hdt⟩ := hv
    refine ⟨fun h' => absurd (hh.symm.trans h') (by decide), fun _ => ?_⟩
    rw [show a + 10 + 2 = a + 12 by omega] at hg hl hdt
    rw [show a + 12 + 3 * K = a + (12 + 3 * K) by omega] at hdt
    exact ⟨hg, hl, hh, hdt⟩

theorem seg_if {pres : ℕ} {acc z : PathSummary} (hz : pres = 0 → z = PathSummary.empty) :
    (if pres = 0 then acc else acc.combine z) = acc.combine z := by
  split_ifs with hp
  · rw [hz hp, PathSummary.combine_empty]
  · rfl

theorem childSumAt_unique {mem : ℕ → ℕ} {h K c : ℕ} {s s' : PathSummary}
    (hs : ChildSumAt pathPayload (pathLayout h K) mem c s)
    (hs' : ChildSumAt pathPayload (pathLayout h K) mem c s') : s = s' := by
  rcases hs with ⟨hc, rfl⟩ | ⟨hc, hs⟩
  · rcases hs' with ⟨-, rfl⟩ | ⟨hc', -⟩
    · rfl
    · exact absurd hc hc'
  · rcases hs' with ⟨hc', -⟩ | ⟨-, hs'⟩
    · exact absurd hc' hc
    · exact pathSummaryAt_unique hs hs'

theorem SegAt.frame {m m' : ℕ → ℕ} {src f b h K heap : ℕ} {z : PathSummary}
    (hs : SegAt m src f b h K z) (hm : ∀ y < heap, m' y = m y) (h1 : src + 2 * K ≤ heap)
    (h2 : f < heap) (h3 : b + K ≤ heap) : SegAt m' src f b h K z :=
  ⟨hs.1.congr fun i hi => hm _ (by omega), hs.2.1.congr fun i hi => hm _ (by omega),
    optIntAt_move hs.2.2 (hm _ h2) fun i hi => hm _ (by omega)⟩

/-- `pathPullBody` meets the pull contract of the path payload. -/
theorem pathPull_meetsContract {w h K f segProc copyProc : ℕ} {p : Program}
    (hb : p.procs[f]? = some (pathPullBody segProc copyProc))
    (hseg : MeetsContract w p segProc (segContract w h K))
    (hcopy : MeetsContract w p copyProc (copyWordsContract w)) :
    MeetsContract w p f
      (pullContract pathPayload (pathLayout h K) (pathOk h K) w (pathCost K) (pathSpace K)) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨x, a, l, r, heap, rfl, hah, hlh, hrh, v, sl, sr, hv₀, hsl, hsr, hok⟩, hz,
    hroom⟩
  change ZeroFrom mem heap at hz
  change heap + (8 * K + 8) < 2 ^ w at hroom
  rw [pathLayout_stride] at hah hlh hrh
  change PathValAt mem (a + 6) h K v at hv₀
  have hK : mem (a + 9) = K := hv₀.2.2.2.1
  have hv : PathEdgeAt mem (a + 10) h K v := hv₀.2.2.2.2
  change PathSummaryFits h K (sl.combine ((PathSummary.single v).combine sr)) at hok
  have acc0 : AccAt mem heap h K PathSummary.empty := accAt_empty fun i hi => hz _ (by omega)
  have hw : 1 < 2 ^ w := by omega
  apply runs_start_le
  unfold pathPullBody
  refine runs_seq_assign_le (Expr.eval_load_of_eq (by eval_expr) hK) ?_
  refine runs_seq_assign_le (v := heap + (3 * K + 1)) (by eval_expr) ?_
  -- the left child
  refine runs_seq_call_le hseg
    (vs := [heap, l + (12 + 4 * K), l + (12 + 6 * K), l + (13 + 6 * K), l, K,
      heap + (3 * K + 1)])
    (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨⟨_, _, _, _, _, _, rfl, le_rfl, by omega, by omega, by omega, _, _, acc0,
      (childSeg hsl).2⟩, show ZeroFrom _ (heap + (3 * K + 1)) from fun y hy => hz y (by omega),
      show heap + (3 * K + 1) + 2 * K < 2 ^ w by omega⟩ ?_
  rintro v₁ m₁ pos₁ ⟨hz₁, hf₁, hp₁⟩
  change ZeroFrom m₁ (heap + (3 * K + 1)) at hz₁
  change ∀ y < heap + (3 * K + 1), ¬ (heap ≤ y ∧ y < heap + (3 * K + 1)) → m₁ y = mem y at hf₁
  have hacc₁ : AccAt m₁ heap h K (PathSummary.empty.combine sl) := by
    rw [← seg_if (childSeg hsl).1]; exact hp₁ _ _ acc0 (childSeg hsl).2
  have hb₁ : ∀ y < heap, m₁ y = mem y := fun y hy => hf₁ y (by omega) (by omega)
  have hv₁ : PathEdgeAt m₁ (a + 10) h K v := pathEdgeAt_move hv fun i hi => hb₁ _ (by omega)
  -- the node's own edge
  refine runs_seq_call_le hseg
    (vs := [heap, a + 12, a + 10, a + (12 + 3 * K), m₁ (a + 10), K, heap + (3 * K + 1)])
    (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy
      rcases hy with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first | omega | skip
      rcases (valSeg hv₁) with ⟨-, -⟩
      cases v with
      | none => rw [show m₁ (a + 10) = 0 from hv₁]; omega
      | some e => rw [hv₁.1]; omega)
    ⟨⟨_, _, _, _, _, _, rfl, le_rfl, by omega, by omega, by omega, _, _, hacc₁,
      (valSeg hv₁).2⟩, show ZeroFrom _ (heap + (3 * K + 1)) from hz₁,
      show heap + (3 * K + 1) + 2 * K < 2 ^ w by omega⟩ ?_
  rintro v₂ m₂ pos₂ ⟨hz₂, hf₂, hp₂⟩
  change ZeroFrom m₂ (heap + (3 * K + 1)) at hz₂
  change ∀ y < heap + (3 * K + 1), ¬ (heap ≤ y ∧ y < heap + (3 * K + 1)) → m₂ y = m₁ y at hf₂
  have hacc₂ : AccAt m₂ heap h K
      ((PathSummary.empty.combine sl).combine (PathSummary.single v)) := by
    rw [← seg_if (valSeg hv₁).1]; exact hp₂ _ _ hacc₁ (valSeg hv₁).2
  have hb₂ : ∀ y < heap, m₂ y = mem y := fun y hy =>
    (hf₂ y (by omega) (by omega)).trans (hb₁ y hy)
  -- the right child
  refine runs_seq_call_le hseg
    (vs := [heap, r + (12 + 4 * K), r + (12 + 6 * K), r + (13 + 6 * K), r, K,
      heap + (3 * K + 1)])
    (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨⟨_, _, _, _, _, _, rfl, le_rfl, by omega, by omega, by omega, _, _, hacc₂,
      fun hr => ((childSeg hsr).2 hr).frame hb₂ (by omega) (by omega) (by omega)⟩,
      show ZeroFrom _ (heap + (3 * K + 1)) from hz₂,
      show heap + (3 * K + 1) + 2 * K < 2 ^ w by omega⟩ ?_
  rintro v₃ m₃ pos₃ ⟨hz₃, hf₃, hp₃⟩
  change ZeroFrom m₃ (heap + (3 * K + 1)) at hz₃
  change ∀ y < heap + (3 * K + 1), ¬ (heap ≤ y ∧ y < heap + (3 * K + 1)) → m₃ y = m₂ y at hf₃
  have hacc₃ : AccAt m₃ heap h K (sl.combine ((PathSummary.single v).combine sr)) := by
    rw [← PathSummary.combine_assoc, ← PathSummary.empty_combine sl, ← seg_if (childSeg hsr).1]
    exact hp₃ _ _ hacc₂ fun hr => ((childSeg hsr).2 hr).frame hb₂ (by omega) (by omega)
      (by omega)
  have hb₃ : ∀ y < heap, m₃ y = mem y := fun y hy =>
    (hf₃ y (by omega) (by omega)).trans (hb₂ y hy)
  have hfin := hacc₃.summary hok
  -- copy the result into the record
  refine runs_seq_call_le hcopy (vs := [heap, a + (12 + 4 * K), 3 * K + 1]) (by eval_expr) (by
      intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, Or.inl (by omega)⟩ ?_
  rintro v₄ m₄ pos₄ ⟨s₄, d₄, l₄, heq₄, -, hc₄, ho₄⟩
  simp only [List.cons.injEq, and_true] at heq₄
  obtain ⟨rfl, rfl, rfl⟩ := heq₄
  change ∀ i < 3 * K + 1, m₄ (a + (12 + 4 * K) + i) = m₃ (heap + i) at hc₄
  change ∀ y, y < a + (12 + 4 * K) ∨ a + (12 + 4 * K) + (3 * K + 1) ≤ y → m₄ y = m₃ y at ho₄
  -- clear the scratch
  refine runs_seq_call_le hcopy (vs := [heap + (3 * K + 1), heap, 3 * K + 1]) (by eval_expr)
    (by intro y hy; simp only [List.mem_cons, List.not_mem_nil, or_false] at hy; omega)
    ⟨_, _, _, rfl, hw, by omega, by omega, Or.inl le_rfl⟩ ?_
  rintro v₅ m₅ pos₅ ⟨s₅, d₅, l₅, heq₅, -, hc₅, ho₅⟩
  simp only [List.cons.injEq, and_true] at heq₅
  obtain ⟨rfl, rfl, rfl⟩ := heq₅
  change ∀ i < 3 * K + 1, m₅ (heap + i) = m₄ (heap + (3 * K + 1) + i) at hc₅
  change ∀ y, y < heap ∨ heap + (3 * K + 1) ≤ y → m₅ y = m₄ y at ho₅
  have hkeep : ∀ y < heap, ¬ (a + (12 + 4 * K) ≤ y ∧ y < a + (12 + 4 * K) + (3 * K + 1)) →
      m₅ y = mem y := fun y hy hn => by
    rw [ho₅ y (by omega), ho₄ y (by omega), hb₃ y hy]
  refine runs_ret_le (by eval_expr) ⟨fun y hy => ?_, fun y hy hn => ?_, ?_⟩ ?_
  · change heap ≤ y at hy
    show m₅ y = 0
    by_cases hy' : y < heap + (3 * K + 1)
    · obtain ⟨i, hi, rfl⟩ : ∃ i, i < 3 * K + 1 ∧ y = heap + i := ⟨y - heap, by omega, by omega⟩
      rw [hc₅ i hi, ho₄ _ (by omega)]
      exact hz₃ _ (by omega)
    · rw [ho₅ y (by omega), ho₄ y (by omega)]; exact hz₃ y (by omega)
  · change y < heap at hy
    change ¬ (a + 6 ≤ y ∧ y < a + (pathLayout h K).nodeStride) at hn
    rw [pathLayout_stride] at hn
    exact hkeep y hy (by omega)
  · intro v' sl' sr' hv' hsl' hsr'
    change PathValAt mem (a + 6) h K v' at hv'
    obtain rfl := pathValAt_unique hv₀ hv'
    obtain rfl := childSumAt_unique hsl hsl'
    obtain rfl := childSumAt_unique hsr hsr'
    refine ⟨?_, ?_, fun t ht => ?_⟩
    · show PathValAt m₅ (a + 6) h K v
      exact pathValAt_move hv₀ fun i hi => hkeep _ (by omega) (by omega)
    · show (pathLayout h K).SumAt m₅ (a + (pathLayout h K).offSum)
        (sl.combine ((PathSummary.single v).combine sr))
      rw [pathLayout_offSum]
      exact pathSummaryAt_move hfin fun i hi => by rw [ho₅ _ (by omega), hc₄ i hi]
    · change (pathLayout h K).TagAt mem (a + (pathLayout h K).offTag) t at ht
      show (pathLayout h K).TagAt m₅ (a + (pathLayout h K).offTag) t
      rw [pathLayout_offTag] at ht ⊢
      exact pathTagAt_move ht fun i hi => hkeep _ (by omega) (by omega)
  · simp only [pathCost, pullContract, segContract, copyWordsContract, payloadContract,
      Expr.size_reg, Expr.size_const, Expr.size_bin, Expr.size_load, argsSize_cons, argsSize_nil,
      kAt, kOff, kSumW]
    omega

end MinCostFlow.LinkCut.Path
