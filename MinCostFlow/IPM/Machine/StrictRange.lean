module

public import MinCostFlow.Num.Less
public import MinCostFlow.IPM.Machine.Layout
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.NormNum

/-!
# A read-only strict capacity guard

The queried candidate and both capacity bounds have the same signed
width. Compare the lower bound with the candidate and the candidate
with the upper bound. The entry returns one exactly when both strict
inequalities hold and preserves every memory cell.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[lower,candidate,upper,L]`. Return a Boolean word. -/
def strictRangeBody (less : ℕ) : Stmt :=
  .call 4 less [.reg 0,.reg 1,.reg 3] ;;
  .call 5 less [.reg 1,.reg 2,.reg 3] ;;
  .ret (.bin .mul (.reg 4) (.reg 5))

/-- Both comparisons use one linked signed comparison module. -/
def strictRangeModule (b h : ℕ) : List Stmt := [strictRangeBody (b+1)] ++ Num.lessModule (b+1) h

/-- The guard reads three valid blocks and returns the exact interval test. -/
def strictRangeContract (w h : ℕ) : Contract where
  pre args mem := ∃ lo x up L,args=[lo,x,up,L] ∧ lo+L < 2^w ∧ x+L < 2^w ∧ up+L < 2^w ∧
    Num.Valid mem lo h L ∧ Num.Valid mem x h L ∧ Num.Valid mem up h L
  post args mem v mem' := mem'=mem ∧ v=if
    Num.intVal mem (args.getD 0 0) h (args.getD 3 0) < Num.intVal mem (args.getD 1 0) h (args.getD 3 0) ∧
    Num.intVal mem (args.getD 1 0) h (args.getD 3 0) < Num.intVal mem (args.getD 2 0) h (args.getD 3 0)
    then 1 else 0
  cost args _ := 82*args.getD 3 0+150

/-- The capacity guard and both signed comparisons are deterministic. -/
theorem strictRangeModule_noRand (b h : ℕ) : ∀ body ∈ strictRangeModule b h,body.NoRand := by
  intro body hb
  simp only [strictRangeModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [strictRangeBody,Stmt.NoRand]
  · exact Num.lessModule_noRand _ _ _ hb

/-- The machine decides the exact strict interval, with both signed
comparisons and their argument evaluation included in its linear cost. -/
theorem strictRange_meetsContract {w h b : ℕ} {p : Program}
    (hh : 0 < h) (hw : 1 < 2^w) (hb : Num.base h < 2^w)
    (hp : p.HasAt b (strictRangeModule b h)) :
    MeetsContract w p b (strictRangeContract w h) := by
  have hl : p.HasAt (b+1) (Num.lessModule (b+1) h) := Num.hasAt_append_right hp
  have hless := Num.less_meetsContract hh hw hb hl
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨lo,x,up,L,rfl,hlo,hx,hup,hvlo,hvx,hvup⟩ := hpre
  have hloW : lo < 2^w := hwords _ (by simp)
  have hxW : x < 2^w := hwords _ (by simp)
  have hupW : up < 2^w := hwords _ (by simp)
  have hLW : L < 2^w := hwords _ (by simp)
  apply runs_start_le
  unfold strictRangeBody
  refine runs_seq_call_le hless (vs:=[lo,x,L]) (by eval_expr) (by wram_words)
    ⟨lo,x,L,rfl,hlo,hx,hvlo,hvx⟩ ?_
  intro v0 mem0 pos0 hp0
  obtain ⟨hm0,hv0⟩ := hp0
  change mem0=mem at hm0
  subst mem0
  change v0=if Num.intVal mem lo h L < Num.intVal mem x h L then 1 else 0 at hv0
  have hv0b : v0 ≤ 1 := by split_ifs at hv0 <;> omega
  refine runs_seq_call_le hless (vs:=[x,up,L]) (by eval_expr) (by wram_words)
    ⟨x,up,L,rfl,hx,hup,hvx,hvup⟩ ?_
  intro v1 mem1 pos1 hp1
  obtain ⟨hm1,hv1⟩ := hp1
  change mem1=mem at hm1
  subst mem1
  change v1=if Num.intVal mem x h L < Num.intVal mem up h L then 1 else 0 at hv1
  have hv1b : v1 ≤ 1 := by split_ifs at hv1 <;> omega
  have hprod : v0*v1 < 2^w := lt_of_le_of_lt (by nlinarith only [hv0b,hv1b]) hw
  refine runs_ret_le (v:=v0*v1) (by eval_expr) ?_ ?_
  · change mem=mem ∧ v0*v1=if Num.intVal mem lo h L < Num.intVal mem x h L ∧
      Num.intVal mem x h L < Num.intVal mem up h L then 1 else 0
    refine ⟨rfl,?_⟩
    rw [hv0,hv1]
    by_cases h0 : Num.intVal mem lo h L < Num.intVal mem x h L <;>
      by_cases h1 : Num.intVal mem x h L < Num.intVal mem up h L <;> simp [h0,h1]
  · simp only [strictRangeContract,Num.lessContract,List.getD_cons_zero,List.getD_cons_succ,
      Expr.size_bin,Expr.size_reg,argsSize_cons,argsSize_nil]
    omega

/-- At any shared fixed-point scale, acceptance is exactly strict
membership in the represented capacity interval. -/
theorem strictRange_output {w h lo xp up L P v : ℕ} {mem mem' : ℕ → ℕ} {lower x upper : ℝ}
    (hout : (strictRangeContract w h).post [lo,xp,up,L] mem v mem')
    (hlo : ScalarAt mem lo h L P lower) (hx : ScalarAt mem xp h L P x)
    (hup : ScalarAt mem up h L P upper) : v=1 ↔ lower < x ∧ x < upper := by
  have hiff : v=1 ↔ Num.intVal mem lo h L < Num.intVal mem xp h L ∧
      Num.intVal mem xp h L < Num.intVal mem up h L := by
    rw [hout.2]
    split_ifs <;> simp_all
  rw [hiff,← hlo.2,← hx.2,← hup.2]
  simp only [Num.fixVal,div_lt_div_iff_of_pos_right (by positivity : (0:ℝ) < 2^P)]
  norm_cast

end MinCostFlow.IPM.Machine
