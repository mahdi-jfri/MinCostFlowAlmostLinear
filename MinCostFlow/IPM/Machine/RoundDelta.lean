module

public import MinCostFlow.IPM.Machine.RoundCompare
public import MinCostFlow.IPM.Machine.RoundPathRead
import WordRAM.Tactic

/-!
# Choosing the amount of a cycle correction

The new edge supplies one directional availability. If the path
has a hit, compare against the selected forest availability and
return the address of the smaller block.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- On [edgeAvailability,pathRecord,L], return the chosen block address. -/
def roundDeltaBody (less : ℕ) : Stmt :=
  .cond (.load (.reg 1))
    (.call 3 less [.bin .add (.reg 1) (.const 4),.reg 0,.reg 2] ;;
     .cond (.reg 3) (.ret (.bin .add (.reg 1) (.const 4))) (.ret (.reg 0)))
    (.ret (.reg 0))

/-- The selected address holds the exact minimum and stays below
the allocated end supplied by the caller. -/
def roundDeltaContract (w h P : ℕ) (q : ℚ) (hit : Option PathHit) : Contract where
  pre args mem := ∃ a b L heap,args=[a,b,L,heap] ∧ 0<L ∧
    a+L≤heap ∧ b+4+2*L≤heap ∧ heap<2^w ∧ RatAt mem a h L P q ∧ PathHitAt mem b h L P hit
  post args mem out final := final=mem ∧ out+args.getD 2 0≤args.getD 3 0 ∧
    RatAt final out h (args.getD 2 0) P (hit.elim q (fun e => min q e.avail)) ∧
    (out=args.getD 0 0 ∨ out=args.getD 1 0+4)
  cost args _ := 41*args.getD 2 0+80

/-- The availability decision uses no random instruction. -/
theorem roundDelta_noRand (less : ℕ) : (roundDeltaBody less).NoRand := by
  simp [roundDeltaBody,Stmt.NoRand]

/-- The actual signed comparison chooses the model minimum, with
the new edge used on ties and on an empty forest path. -/
theorem roundDelta_meetsContract {w h P entry less : ℕ} {p : Program}
    (hBody : p.procs[entry]?=some (roundDeltaBody less))
    (hLess : MeetsContract w p less (Num.lessContract w h))
    (q : ℚ) (hit : Option PathHit) : MeetsContract w p entry (roundDeltaContract w h P q hit) := by
  apply meetsContract_of_runs hBody
  intro args mem pos ω hw hpre
  obtain ⟨a,b,L,heap,rfl,hL,ha,hb,hh,hq,hHit⟩ := hpre
  have h₁ : 1<2^w := by omega
  have h₄ : 4<2^w := by omega
  have hB4 : b+4<2^w := by omega
  have hB4L : b+4+L<2^w := by omega
  have hAL : a+L<2^w := by omega
  have hEval : (Expr.load (.reg 1)).eval w (startState [a,b,L,heap] mem pos)=some (mem b) := by eval_expr
  unfold roundDeltaBody
  apply runs_start_le
  cases hit with
  | none =>
    have hr : mem b=0 := hHit
    rw [hr] at hEval
    refine runs_cond_le hEval (fun hn => (hn rfl).elim) ?_
    intro _
    exact runs_ret_le (v:=a) rfl ⟨rfl,ha,hq,Or.inl rfl⟩ (by simp [roundDeltaContract])
  | some hit =>
    rw [(pathHit_words hHit).1] at hEval
    refine runs_cond_le hEval ?_ (fun he => by contradiction)
    intro _
    refine runs_seq_call_le hLess (vs:=[b+4,a,L]) (by eval_expr) (by wram_words) ?_ ?_
    · exact ⟨b+4,a,L,rfl,by omega,by omega,hHit.2.1.1,hq.1⟩
    · intro r final pos' hout
      obtain ⟨hFinal,hr⟩ := hout
      have he : final=mem := hFinal
      subst final
      change r=(if Num.intVal mem (b+4) h L<Num.intVal mem a h L then 1 else 0) at hr
      simp only [hHit.2.1.lt_iff hq] at hr
      have hR : (Expr.reg 3).eval w
          ⟨mem,Function.update (startState [a,b,L,heap] mem pos).regs 3 r,pos'⟩=some r := by simp [Expr.eval]
      by_cases hl : hit.avail<q
      · rw [ite_eq_left hl] at hr
        refine runs_cond_le hR ?_ (fun hz => by omega)
        intro _
        refine runs_ret_le (v:=b+4) (by eval_expr) ?_ ?_
        · change mem=mem ∧ b+4+L≤heap ∧ RatAt mem (b+4) h L P (min q hit.avail) ∧ (b+4=a ∨ b+4=b+4)
          exact ⟨rfl,by omega,by simpa [min_eq_right hl.le] using hHit.2.1,Or.inr rfl⟩
        · simp only [roundDeltaContract,Num.lessContract,List.getD_cons_zero,List.getD_cons_succ,
            Expr.size_reg,Expr.size_bin,Expr.size_const,Expr.size_load,argsSize_cons,argsSize_nil]
          omega
      · rw [ite_eq_right hl] at hr
        refine runs_cond_le hR (fun hn => (hn hr).elim) ?_
        intro _
        refine runs_ret_le (v:=a) rfl ?_ ?_
        · change mem=mem ∧ a+L≤heap ∧ RatAt mem a h L P (min q hit.avail) ∧ (a=a ∨ a=b+4)
          exact ⟨rfl,ha,by simpa [min_eq_left (le_of_not_gt hl)] using hq,Or.inl rfl⟩
        · simp only [roundDeltaContract,Num.lessContract,List.getD_cons_zero,List.getD_cons_succ,
            Expr.size_reg,Expr.size_bin,Expr.size_const,Expr.size_load,argsSize_cons,argsSize_nil]
          omega

end MinCostFlow.IPM.Machine
