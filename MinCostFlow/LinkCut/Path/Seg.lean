module

public import MinCostFlow.LinkCut.Path.Max
public import MinCostFlow.LinkCut.Path.Act

/-!
# Adding one path segment to a running summary

The pull step of the path payload builds the new summary of a node in scratch memory, one path
segment at a time: the left child's path, the node's own edge, the right child's path.
`segBody` adds one segment to the running summary: it adds the two sums with `addBlock` and
takes the detector maximum with `maxIntoBody`.

The running sums may leave the range of `K` limbs before the last segment brings them back, so
the scratch holds them modulo the capacity (`AccAt`). Since `wrap (wrap a + b) = wrap (a + b)`,
the final value is still exact when it fits.
-/

@[expose] public section

namespace MinCostFlow.LinkCut.Path

open WordRAM MinCostFlow.Num MinCostFlow.MinRatio MinCostFlow.LinkCut.Gen

/-- A running summary at `S`: the two sums modulo the capacity, then the detector maximum. -/
def AccAt (mem : ℕ → ℕ) (S h K : ℕ) (acc : PathSummary) : Prop :=
  PathIntAt mem S h K (wrap h K acc.gradient) ∧
  PathIntAt mem (S + K) h K (wrap h K acc.length) ∧
  OptIntAt mem (S + 2 * K) (S + 2 * K + 1) h K acc.detector

/-- A segment: its two sums at `src` and `src + K`, its detector maximum at `f` and `b`. -/
def SegAt (mem : ℕ → ℕ) (src f b h K : ℕ) (z : PathSummary) : Prop :=
  PathIntAt mem src h K z.gradient ∧ PathIntAt mem (src + K) h K z.length ∧
  OptIntAt mem f b h K z.detector

theorem wrap_wrap_add (h K : ℕ) (x y : ℤ) : wrap h K (wrap h K x + y) = wrap h K (x + y) := by
  rw [add_comm, wrap_add_wrap, add_comm]

/-- Fresh zero memory holds the empty running summary. -/
theorem accAt_empty {mem : ℕ → ℕ} {S h K : ℕ} (hz : ∀ i < 3 * K + 1, mem (S + i) = 0) :
    AccAt mem S h K PathSummary.empty := by
  have hblk : ∀ j, j + K ≤ 2 * K → PathIntAt mem (S + j) h K 0 := fun j hj =>
    ⟨fun i hi => by rw [Nat.add_assoc, hz _ (by omega)]; exact base_pos h,
      intVal_zero fun i hi => by rw [Nat.add_assoc]; exact hz _ (by omega)⟩
  have hw0 : wrap h K 0 = 0 := wrap_of_fits ⟨by have := capacity_pos h K; omega,
    by have := capacity_pos h K; omega⟩
  refine ⟨?_, ?_, ?_⟩
  · have := hblk 0 (by omega)
    simp only [Nat.add_zero] at this
    simpa [PathSummary.empty, hw0] using this
  · have := hblk K (by omega)
    simpa [PathSummary.empty, hw0] using this
  · exact hz (2 * K) (by omega)

/-- A running summary whose sums fit is a summary. -/
theorem AccAt.summary {mem : ℕ → ℕ} {S h K : ℕ} {s : PathSummary} (ha : AccAt mem S h K s)
    (hf : PathSummaryFits h K s) : PathSummaryAt mem S h K s := by
  obtain ⟨hg, hl, hd⟩ := ha
  rw [wrap_of_fits hf.1] at hg
  rw [wrap_of_fits hf.2.1] at hl
  exact pathSummaryAt_iff.mpr ⟨hg, hl, hd⟩

/-- `seg [S, src, f, b, pres, K, heap]`: if `pres` is not zero, add the segment at `src`, `f`,
`b` to the running summary at `S`. -/
def segBody (addProc maxProc : ℕ) : Stmt :=
  .cond (.reg 4)
    (.call 7 addProc [.reg 0, .reg 1, .reg 5, .reg 6] ;;
     .call 7 addProc [.bin .add (.reg 0) (.reg 5), .bin .add (.reg 1) (.reg 5), .reg 5, .reg 6] ;;
     .call 7 maxProc [.bin .add (.reg 0) (.bin .mul (.const 2) (.reg 5)), .reg 2, .reg 3, .reg 5] ;;
     .ret (.const 0))
    (.ret (.const 0))

theorem segBody_noRand (a b : ℕ) : (segBody a b).NoRand := by
  simp [segBody, Stmt.NoRand]

/-- The contract of `segBody`. The segment lies below the running summary, which lies below the
heap pointer. -/
def segContract (w h K : ℕ) : Contract :=
  payloadContract w
    (fun args mem => ∃ S src f b pres heap, args = [S, src, f, b, pres, K, heap] ∧
      S + (3 * K + 1) ≤ heap ∧ src + 2 * K ≤ S ∧ f < S ∧ b + K ≤ S ∧
      ∃ acc z, AccAt mem S h K acc ∧ (pres ≠ 0 → SegAt mem src f b h K z))
    (fun args y => args.getD 0 0 ≤ y ∧ y < args.getD 0 0 + (3 * K + 1))
    (fun args mem _ mem' => ∀ acc z, AccAt mem (args.getD 0 0) h K acc →
      (args.getD 4 0 ≠ 0 → SegAt mem (args.getD 1 0) (args.getD 2 0) (args.getD 3 0) h K z) →
      AccAt mem' (args.getD 0 0) h K (if args.getD 4 0 = 0 then acc else acc.combine z))
    (260 * K + 300) (2 * K)

theorem seg_meetsContract {w h K f addProc maxProc : ℕ} {p : Program}
    (hb : p.procs[f]? = some (segBody addProc maxProc))
    (hadd : MeetsContract w p addProc (addBlockContract w h K))
    (hmax : MeetsContract w p maxProc (maxIntoContract w h K)) :
    MeetsContract w p f (segContract w h K) := by
  apply meetsContract_of_runs hb
  intro args mem pos ω hwords hpre
  rcases hpre with ⟨⟨S, src, fl, b, pres, heap, rfl, hSh, hsrc, hfl, hbS, acc, z, hacc, hseg⟩,
    hz, hroom⟩
  change ZeroFrom mem heap at hz
  change heap + 2 * K < 2 ^ w at hroom
  have hcost : ∀ c, c ≤ 260 * K + 300 → c ≤ (segContract w h K).cost [S, src, fl, b, pres, K, heap] mem :=
    fun c hc => hc
  apply runs_start_le
  unfold segBody
  refine runs_cond_le (v := pres) (by eval_expr) ?_ ?_
  · intro hp
    obtain ⟨zg, zl, zd⟩ := hseg hp
    obtain ⟨ag, al, ad⟩ := hacc
    refine runs_seq_addBlock (x := S) (d := src) (heap := heap) hadd (by eval_expr)
      (by omega) (by omega) (by omega) (by omega) (by omega) ag.1 zg.1 hz hroom ?_
    intro m₁ hz₁ hf₁ hv₁ hval₁ v₁ pos₁
    change intVal m₁ S h K = wrap h K (intVal mem S h K + intVal mem src h K) at hval₁
    have hg₁ : PathIntAt m₁ S h K (wrap h K (acc.gradient + z.gradient)) :=
      ⟨hv₁, by rw [hval₁, ag.2, zg.2, wrap_wrap_add]⟩
    have al₁ := al.congr fun i hi => hf₁ _ (by omega) (by omega)
    have zl₁ := zl.congr fun i hi => hf₁ _ (by omega) (by omega)
    refine runs_seq_addBlock (x := S + K) (d := src + K) (heap := heap) hadd (by eval_expr)
      (by omega) (by omega) (by omega) (by omega) (by omega) al₁.1 zl₁.1 hz₁ hroom ?_
    intro m₂ hz₂ hf₂ hv₂ hval₂ v₂ pos₂
    dsimp only at hf₂ hval₂
    have hl₂ : PathIntAt m₂ (S + K) h K (wrap h K (acc.length + z.length)) :=
      ⟨hv₂, by rw [hval₂, al₁.2, zl₁.2, wrap_wrap_add]⟩
    have hkeep : ∀ y < heap, ¬ (S ≤ y ∧ y < S + 2 * K) → m₂ y = mem y := fun y hy hn =>
      (hf₂ y hy (by omega)).trans (hf₁ y hy (by omega))
    have ad₂ : OptIntAt m₂ (S + 2 * K) (S + 2 * K + 1) h K acc.detector :=
      optIntAt_move ad (hkeep _ (by omega) (by omega))
        fun i hi => hkeep _ (by omega) (by omega)
    have zd₂ : OptIntAt m₂ fl b h K z.detector :=
      optIntAt_move zd (hkeep _ (by omega) (by omega))
        fun i hi => hkeep _ (by omega) (by omega)
    refine runs_seq_call_le hmax (vs := [S + 2 * K, fl, b, K]) (by eval_expr) (by
      intro x hx; simp only [List.mem_cons, List.not_mem_nil, or_false] at hx; omega)
      ⟨_, _, _, rfl, by omega, by omega, by omega, by omega, Or.inl (by omega),
        Or.inl (by omega), _, _, ad₂, zd₂⟩ ?_
    rintro v₃ m₃ pos₃ ⟨hf₃, hmax₃⟩
    simp only [List.getD_cons_zero, List.getD_cons_succ] at hf₃ hmax₃
    have hd₃ := hmax₃ _ _ ad₂ zd₂
    refine runs_ret_le (by eval_expr) ⟨fun y hy => ?_, fun y hy hn => ?_, ?_⟩
      (hcost _ (by simp only [addBlockContract, maxIntoContract, payloadContract,
        Expr.size_reg, Expr.size_const, Expr.size_bin, argsSize_cons, argsSize_nil,
        List.getD_cons_zero, List.getD_cons_succ] at *; omega))
    · change heap ≤ y at hy
      show m₃ y = 0
      rw [hf₃ y (by omega)]; exact hz₂ y hy
    · change y < heap at hy
      change ¬ (S ≤ y ∧ y < S + (3 * K + 1)) at hn
      show m₃ y = mem y
      rw [hf₃ y (by omega)]; exact hkeep y hy (by omega)
    · intro acc' z' hacc' hseg'
      simp only [List.getD_cons_zero, List.getD_cons_succ] at hacc' hseg' ⊢
      obtain ⟨ag', al', ad'⟩ := hacc'
      obtain ⟨zg', zl', zd'⟩ := hseg' hp
      rw [if_neg hp]
      refine ⟨?_, ?_, ?_⟩
      · show PathIntAt m₃ S h K (wrap h K (acc'.gradient + z'.gradient))
        rw [← (zg.unique zg' : z.gradient = z'.gradient)]
        have hw : wrap h K acc.gradient = wrap h K acc'.gradient := ag.unique ag'
        rw [← wrap_wrap_add, ← hw, wrap_wrap_add]
        exact hg₁.congr fun i hi => by rw [hf₃ _ (by omega), hf₂ _ (by omega) (by omega)]
      · show PathIntAt m₃ (S + K) h K (wrap h K (acc'.length + z'.length))
        rw [← (zl.unique zl' : z.length = z'.length)]
        have hw : wrap h K acc.length = wrap h K acc'.length := al.unique al'
        rw [← wrap_wrap_add, ← hw, wrap_wrap_add]
        exact hl₂.congr fun i hi => hf₃ _ (by omega)
      · show OptIntAt m₃ (S + 2 * K) (S + 2 * K + 1) h K
          (detectorMax acc'.detector z'.detector)
        rw [← optIntAt_unique ad ad', ← optIntAt_unique zd zd']
        exact hd₃
  · intro hp
    subst hp
    refine runs_ret_le (by eval_expr) ⟨hz, fun _ _ _ => rfl, ?_⟩
      (hcost _ (by simp only [Expr.size_reg, Expr.size_const]; omega))
    intro acc' z' hacc' _
    simpa [startState] using hacc'

end MinCostFlow.LinkCut.Path
