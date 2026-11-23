module

public import MinCostFlow.LinkCut.Path.Rev
public import MinCostFlow.Num.Less
public import WordRAM.CopyWords
public import MinCostFlow.LinkCut.Gen.Call

/-!
# The detector maximum of the path payload

A summary keeps the largest detector value of its path, or nothing for a path without edges.
In memory this is a flag word and a number block (`OptIntAt`). `maxIntoBody` replaces such a
pair by the maximum of itself and another pair (`detectorMax`): it copies the other number when
there is no number yet, or when the other number is larger. The values are only copied, so no
number can overflow here.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen

/-- An optional number: flag `0` at `f` for none, or flag `1` at `f` and the number at `b`. -/
def OptIntAt (mem : ℕ → ℕ) (f b h K : ℕ) : Option ℤ → Prop
  | none => mem f = 0
  | some z => mem f = 1 ∧ PathIntAt mem b h K z

theorem optIntAt_unique {m : ℕ → ℕ} {f b h K : ℕ} {z z' : Option ℤ}
    (hz : OptIntAt m f b h K z) (hz' : OptIntAt m f b h K z') : z = z' := by
  cases z with
  | none =>
    cases z' with
    | none => rfl
    | some y => exact absurd (hz'.1.symm.trans hz) (by decide)
  | some y =>
    cases z' with
    | none => exact absurd (hz.1.symm.trans hz') (by decide)
    | some y' => rw [hz.2.unique hz'.2]

theorem optIntAt_move {m m' : ℕ → ℕ} {f b f' b' h K : ℕ} {z : Option ℤ}
    (hz : OptIntAt m f b h K z) (hf : m' f' = m f) (hb : ∀ i < K, m' (b' + i) = m (b + i)) :
    OptIntAt m' f' b' h K z := by
  cases z with
  | none => exact hf.trans hz
  | some y => exact ⟨hf.trans hz.1, hz.2.congr hb⟩

/-- The detector part of a summary is an optional number right after its two sums. -/
theorem pathSummaryAt_iff {m : ℕ → ℕ} {a h K : ℕ} {s : PathSummary} :
    PathSummaryAt m a h K s ↔ PathIntAt m a h K s.gradient ∧
      PathIntAt m (a + K) h K s.length ∧ OptIntAt m (a + 2 * K) (a + 2 * K + 1) h K s.detector := by
  unfold PathSummaryAt
  cases s.detector <;> rfl

theorem detectorMax_none_right (z : Option ℤ) : detectorMax z none = z := by
  cases z <;> rfl

/-- `maxInto [D, f, b, K]`: the pair at `D`, `D + 1` becomes the maximum of itself and the pair at
`f`, `b`. -/
def maxIntoBody (lessProc copyProc : ℕ) : Stmt :=
  .cond (.load (.reg 1))
    (.cond (.load (.reg 0))
      (.call 4 lessProc [.bin .add (.reg 0) (.const 1), .reg 2, .reg 3] ;;
       .cond (.reg 4)
         (.call 4 copyProc [.reg 2, .bin .add (.reg 0) (.const 1), .reg 3] ;;
          .ret (.const 0))
         (.ret (.const 0)))
      (.store (.reg 0) (.const 1) ;;
       .call 4 copyProc [.reg 2, .bin .add (.reg 0) (.const 1), .reg 3] ;;
       .ret (.const 0)))
    (.ret (.const 0))

theorem maxIntoBody_noRand (a b : ℕ) : (maxIntoBody a b).NoRand := by
  simp [maxIntoBody, Stmt.NoRand]

/-- The contract of `maxIntoBody`. Only the pair at `D` changes. -/
def maxIntoContract (w h K : ℕ) : Contract where
  pre args mem := ∃ D f b, args = [D, f, b, K] ∧ 1 < 2 ^ w ∧ D + 1 + K < 2 ^ w ∧ b + K < 2 ^ w ∧
    f < 2 ^ w ∧ (b + K ≤ D ∨ D + 1 + K ≤ b) ∧ (f < D ∨ D + 1 + K ≤ f) ∧
    ∃ zd zs, OptIntAt mem D (D + 1) h K zd ∧ OptIntAt mem f b h K zs
  post args mem _ mem' :=
    (∀ y, ¬ (args.getD 0 0 ≤ y ∧ y < args.getD 0 0 + 1 + K) → mem' y = mem y) ∧
    ∀ zd zs, OptIntAt mem (args.getD 0 0) (args.getD 0 0 + 1) h K zd →
      OptIntAt mem (args.getD 1 0) (args.getD 2 0) h K zs →
      OptIntAt mem' (args.getD 0 0) (args.getD 0 0 + 1) h K (detectorMax zd zs)
  cost _ _ := 100 * K + 100

theorem maxInto_meetsContract {w h K f lessProc copyProc : ℕ} {p : Program}
    (hb : p.procs[f]? = some (maxIntoBody lessProc copyProc))
    (hless : MeetsContract w p lessProc (lessContract w h))
    (hcopy : MeetsContract w p copyProc (copyWordsContract w)) :
    MeetsContract w p f (maxIntoContract w h K) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨D, fl, b, rfl, hw, hDw, hbw, hfw, hbD, hfD, zd, zs, hzd, hzs⟩
  -- The post, from the final memory.
  have post : ∀ m : ℕ → ℕ, (∀ y, ¬ (D ≤ y ∧ y < D + 1 + K) → m y = mem y) →
      OptIntAt m D (D + 1) h K (detectorMax zd zs) →
      (maxIntoContract w h K).post [D, fl, b, K] mem 0 m := by
    intro m hm hr
    refine ⟨hm, fun zd' zs' hzd' hzs' => ?_⟩
    obtain rfl := optIntAt_unique hzd hzd'
    obtain rfl := optIntAt_unique hzs hzs'
    exact hr
  have hcost : ∀ c, c ≤ 100 * K + 100 → c ≤ (maxIntoContract w h K).cost [D, fl, b, K] mem :=
    fun c hc => hc
  apply runs_start_le
  unfold maxIntoBody
  refine runs_cond_le (v := mem fl) (by eval_expr) ?_ ?_
  · intro hfl
    cases zs with
    | none => exact absurd hzs hfl
    | some z =>
    obtain ⟨-, hz⟩ := hzs
    refine runs_cond_le (v := mem D) (by eval_expr) ?_ ?_
    · intro hD
      cases zd with
      | none => exact absurd hzd hD
      | some y =>
      obtain ⟨hD1, hy⟩ := hzd
      refine runs_seq_call_le hless (vs := [D + 1, b, K]) (by eval_expr) (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
        ⟨_, _, _, rfl, by omega, by omega, hy.1, hz.1⟩ ?_
      rintro v₁ mem₁ pos₁ ⟨hm₁, hv₁⟩
      subst mem₁
      simp only [startState, List.getD_cons_zero, List.getD_cons_succ, hy.2, hz.2] at hv₁
      refine runs_cond_le (v := v₁) (by eval_expr) ?_ ?_
      · intro hv
        have hlt : y < z := by by_contra hc; simp [hc] at hv₁; exact hv hv₁
        refine runs_seq_call_le hcopy (vs := [b, D + 1, K]) (by eval_expr) (by
          intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
          ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
        rintro v₂ mem₂ pos₂ ⟨s₂, d₂, l₂, heq₂, -, hc₂, ho₂⟩
        simp only [List.cons.injEq, and_true] at heq₂
        obtain ⟨rfl, rfl, rfl⟩ := heq₂
        refine runs_ret_le (by eval_expr) (post mem₂ (fun y hy => ho₂ y (by omega)) ?_)
          (hcost _ (by simp only [lessContract, copyWordsContract, Expr.size_reg,
            Expr.size_const, Expr.size_bin, Expr.size_load, argsSize_cons, argsSize_nil,
            List.getD_cons_zero, List.getD_cons_succ]; omega))
        refine ⟨by rw [ho₂ D (by omega)]; exact hD1, ?_⟩
        rw [max_eq_right hlt.le]
        exact hz.congr fun i hi => hc₂ i hi
      · intro hv
        have hle : z ≤ y := by
          by_contra hc; rw [ite_eq_left_iff.mpr (fun h' => absurd (lt_of_not_ge hc) h')] at hv₁; omega
        refine runs_ret_le (by eval_expr) (post mem (fun _ _ => rfl) ⟨hD1, ?_⟩)
          (hcost _ (by simp only [lessContract, Expr.size_reg,
            Expr.size_const, Expr.size_bin, Expr.size_load, argsSize_cons, argsSize_nil,
            List.getD_cons_zero, List.getD_cons_succ]; omega))
        rw [max_eq_left hle]; exact hy
    · intro hD
      cases zd with
      | some y => exact absurd (hzd.1.symm.trans hD) (by decide)
      | none =>
      refine runs_seq_store_named_le (x := D) (v := 1) (by eval_expr) (by eval_expr) ?_
      intro M hM
      have hMy : ∀ y, y ≠ D → M y = mem y := fun y hy => by
        rw [hM]; exact Function.update_of_ne hy _ _
      refine runs_seq_call_le hcopy (vs := [b, D + 1, K]) (by eval_expr) (by
        intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
        ⟨_, _, _, rfl, hw, by omega, by omega, by omega⟩ ?_
      rintro v₂ mem₂ pos₂ ⟨s₂, d₂, l₂, heq₂, -, hc₂, ho₂⟩
      simp only [List.cons.injEq, and_true] at heq₂
      obtain ⟨rfl, rfl, rfl⟩ := heq₂
      refine runs_ret_le (by eval_expr) (post mem₂ (fun y hy => by
          rw [ho₂ y (by omega)]; exact hMy y (by omega)) ?_)
        (hcost _ (by simp only [copyWordsContract, Expr.size_reg,
          Expr.size_const, Expr.size_bin, Expr.size_load, argsSize_cons, argsSize_nil,
          List.getD_cons_zero, List.getD_cons_succ]; omega))
      refine ⟨by rw [ho₂ D (by omega)]; show M D = 1; rw [hM]; exact Function.update_self _ _ _, ?_⟩
      exact hz.congr fun i hi => by rw [hc₂ i hi]; exact hMy _ (by omega)
  · intro hfl
    cases zs with
    | some z => exact absurd (hzs.1.symm.trans hfl) (by decide)
    | none =>
    refine runs_ret_le (by eval_expr) (post mem (fun _ _ => rfl) ?_)
      (hcost _ (by simp only [Expr.size_reg, Expr.size_const, Expr.size_load]; omega))
    rw [detectorMax_none_right]; exact hzd

end MinCostFlow.LinkCut.Path
