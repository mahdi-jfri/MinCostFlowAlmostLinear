module

public import MinCostFlow.IPM.Machine.StrictRange
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic

/-!
# Stopping and range guards for a target residual

Read the exact residual and the represented quarter threshold. A residual
at or below the threshold stops successfully. A larger residual must pass
the numerical range guard before division or gradient evaluation. Return
codes are zero for stopping, one for continuing, and two for rejecting
the target test. Every comparison is signed and preserves memory.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[residual,minimum,maximum,quarter,L]`. -/
def residualGuardBody (less range : ℕ) : Stmt :=
  .call 5 less [.reg 3,.reg 0,.reg 4] ;;
  .cond (.reg 5)
    (.call 6 range [.reg 1,.reg 0,.reg 2,.reg 4] ;;
      .cond (.reg 6) (.ret (.const 1)) (.ret (.const 2)))
    (.ret (.const 0))

/-- Reuse the signed comparator inside the strict range module. -/
def residualGuardModule (b h : ℕ) : List Stmt :=
  [residualGuardBody (b+2) (b+1)] ++ strictRangeModule (b+1) h

/-- Signed exact stopping and numerical-range decisions, with no writes. -/
def residualGuardContract (w h : ℕ) : Contract where
  pre args mem := ∃ r mn mx q L,args=[r,mn,mx,q,L] ∧ r+L < 2^w ∧ mn+L < 2^w ∧
    mx+L < 2^w ∧ q+L < 2^w ∧ Num.Valid mem r h L ∧ Num.Valid mem mn h L ∧
    Num.Valid mem mx h L ∧ Num.Valid mem q h L
  post args mem v mem' := mem'=mem ∧ v=if
    Num.intVal mem (args.getD 0 0) h (args.getD 4 0) ≤ Num.intVal mem (args.getD 3 0) h (args.getD 4 0)
    then 0 else if Num.intVal mem (args.getD 1 0) h (args.getD 4 0) <
      Num.intVal mem (args.getD 0 0) h (args.getD 4 0) ∧
      Num.intVal mem (args.getD 0 0) h (args.getD 4 0) < Num.intVal mem (args.getD 2 0) h (args.getD 4 0)
    then 1 else 2
  cost args _ := 130*args.getD 4 0+300

/-- Both signed guards and every return branch are deterministic. -/
theorem residualGuardModule_noRand (b h : ℕ) : ∀ body ∈ residualGuardModule b h,body.NoRand := by
  intro body hb
  simp only [residualGuardModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [residualGuardBody,Stmt.NoRand]
  · exact strictRangeModule_noRand _ _ _ hb

/-- Actual signed comparisons select the exact stopping, continuation
or rejection code with both guards included in the linear cost bound. -/
theorem residualGuard_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 2 < 2^w) (hb : Num.base h < 2^w)
    (hp : p.HasAt b (residualGuardModule b h)) :
    MeetsContract w p b (residualGuardContract w h) := by
  have hg : p.HasAt (b+1) (strictRangeModule (b+1) h) := Num.hasAt_append_right hp
  have hl : p.HasAt (b+2) (Num.lessModule (b+2) h) := by
    simpa [Nat.add_assoc] using Num.hasAt_append_right hg
  have hw1 : 1 < 2^w := by omega
  have hgSpec := strictRange_meetsContract hh hw1 hb hg
  have hlSpec := Num.less_meetsContract hh hw1 hb hl
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨r,mn,mx,q,L,rfl,hr,hmn,hmx,hq,hvr,hvmn,hvmx,hvq⟩ := hpre
  have hrW : r < 2^w := hwords _ (by simp)
  have hmnW : mn < 2^w := hwords _ (by simp)
  have hmxW : mx < 2^w := hwords _ (by simp)
  have hqW : q < 2^w := hwords _ (by simp)
  have hLW : L < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold residualGuardBody
  refine runs_seq_call_le hlSpec (vs:=[q,r,L]) (by eval_expr) (by wram_words)
    ⟨q,r,L,rfl,hq,hr,hvq,hvr⟩ ?_
  intro b0 mem0 pos0 hp0
  obtain ⟨hm0,hb0⟩ := hp0
  change mem0=mem at hm0
  subst mem0
  change b0=if Num.intVal mem q h L < Num.intVal mem r h L then 1 else 0 at hb0
  have hb0W : b0 < 2^w := by split_ifs at hb0 <;> omega
  refine runs_cond_le (v:=b0) (by eval_expr) ?_ ?_
  · intro hnonzero
    have hlt : Num.intVal mem q h L < Num.intVal mem r h L := by
      split_ifs at hb0 with hlt
      · exact hlt
      · contradiction
    have hnot : ¬ Num.intVal mem r h L ≤ Num.intVal mem q h L := not_le.mpr hlt
    refine runs_seq_call_le hgSpec (vs:=[mn,r,mx,L]) (by eval_expr) (by wram_words)
      ⟨mn,r,mx,L,rfl,hmn,hr,hmx,hvmn,hvr,hvmx⟩ ?_
    intro b1 mem1 pos1 hp1
    obtain ⟨hm1,hb1⟩ := hp1
    change mem1=mem at hm1
    subst mem1
    change b1=if Num.intVal mem mn h L < Num.intVal mem r h L ∧
      Num.intVal mem r h L < Num.intVal mem mx h L then 1 else 0 at hb1
    have hb1W : b1 < 2^w := by split_ifs at hb1 <;> omega
    refine runs_cond_le (v:=b1) (by eval_expr) ?_ ?_
    · intro hnonzero1
      have hinside : Num.intVal mem mn h L < Num.intVal mem r h L ∧
          Num.intVal mem r h L < Num.intVal mem mx h L := by
        split_ifs at hb1 with hi
        · exact hi
        · contradiction
      refine runs_ret_le (v:=1) (by eval_expr) ?_ ?_
      · change mem=mem ∧ 1=if Num.intVal mem r h L ≤ Num.intVal mem q h L then 0 else
          if Num.intVal mem mn h L < Num.intVal mem r h L ∧ Num.intVal mem r h L < Num.intVal mem mx h L then 1 else 2
        simp only [hnot,hinside,↓reduceIte,and_self]
      · simp only [residualGuardContract,Num.lessContract,strictRangeContract,List.getD_cons_zero,
          List.getD_cons_succ,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil]
        omega
    · intro hzero1
      have houtside : ¬ (Num.intVal mem mn h L < Num.intVal mem r h L ∧
          Num.intVal mem r h L < Num.intVal mem mx h L) := by
        intro hi
        rw [ite_eq_left hi] at hb1
        omega
      refine runs_ret_le (v:=2) (by eval_expr) ?_ ?_
      · change mem=mem ∧ 2=if Num.intVal mem r h L ≤ Num.intVal mem q h L then 0 else
          if Num.intVal mem mn h L < Num.intVal mem r h L ∧ Num.intVal mem r h L < Num.intVal mem mx h L then 1 else 2
        simp only [hnot,houtside,↓reduceIte,and_self]
      · simp only [residualGuardContract,Num.lessContract,strictRangeContract,List.getD_cons_zero,
          List.getD_cons_succ,Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil]
        omega
  · intro hzero
    have hstop : Num.intVal mem r h L ≤ Num.intVal mem q h L := by
      by_contra hn
      rw [ite_eq_left (lt_of_not_ge hn)] at hb0
      omega
    refine runs_ret_le (v:=0) (by eval_expr) ?_ ?_
    · change mem=mem ∧ 0=if Num.intVal mem r h L ≤ Num.intVal mem q h L then 0 else _
      simp only [hstop,↓reduceIte,and_self]
    · simp only [residualGuardContract,Num.lessContract,List.getD_cons_zero,List.getD_cons_succ,
        Expr.size_reg,Expr.size_const,argsSize_cons,argsSize_nil]
      omega

/-- Decoding at any common fixed-point scale gives the exact real
stopping threshold and numerical range branches. -/
theorem residualGuard_output {w h rp mn mx qp L P v : ℕ} {mem mem' : ℕ → ℕ}
    {r minimum maximum quarter : ℝ}
    (hout : (residualGuardContract w h).post [rp,mn,mx,qp,L] mem v mem')
    (hr : ScalarAt mem rp h L P r) (hmn : ScalarAt mem mn h L P minimum)
    (hmx : ScalarAt mem mx h L P maximum) (hq : ScalarAt mem qp h L P quarter) :
    v=if r ≤ quarter then 0 else if minimum < r ∧ r < maximum then 1 else 2 := by
  have hcode := hout.2
  change v=if Num.intVal mem rp h L ≤ Num.intVal mem qp h L then 0 else
    if Num.intVal mem mn h L < Num.intVal mem rp h L ∧ Num.intVal mem rp h L < Num.intVal mem mx h L then 1 else 2 at hcode
  have hle : Num.intVal mem rp h L ≤ Num.intVal mem qp h L ↔ r ≤ quarter := by
    rw [← hr.2,← hq.2]
    simp only [Num.fixVal,div_le_div_iff_of_pos_right (by positivity : (0:ℝ) < 2^P)]
    norm_cast
  have hstrict : (Num.intVal mem mn h L < Num.intVal mem rp h L ∧
      Num.intVal mem rp h L < Num.intVal mem mx h L) ↔ minimum < r ∧ r < maximum := by
    rw [← hr.2,← hmn.2,← hmx.2]
    simp only [Num.fixVal,div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < 2^P)]
    norm_cast
  simpa only [hle,hstrict] using hcode

end MinCostFlow.IPM.Machine
