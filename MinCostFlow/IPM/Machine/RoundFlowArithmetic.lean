module

public import MinCostFlow.IPM.Machine.RoundRatFacts
public import MinCostFlow.Num.Add
import WordRAM.Tactic

/-!
# Exact flow update for the new edge of a cycle

The direction bit chooses addition or subtraction of the
same-scale path increment. In either case the updated coordinate
occupies the final block of the allocated result.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- On [flow,delta,L,backward,heap], compute the new flow. -/
def roundFlowArithmeticBody (add subtract : ℕ) : Stmt :=
  .cond (.reg 3)
    (.call 5 subtract [.reg 0,.reg 1,.reg 2,.reg 4] ;; .ret (.reg 5))
    (.call 5 add [.reg 0,.reg 1,.reg 2,.reg 4] ;; .ret (.reg 5))

/-- The exact new rational at the end of a bounded allocation. -/
def roundFlowArithmeticContract (w h P : ℕ) (q δ : ℚ) (backward : Bool) : Contract :=
  let value := if backward then q-δ else q+δ
  let C := heapContract w
    (fun args mem => ∃ a d L heap,args=[a,d,L,backward.toNat,heap] ∧
      a+L≤heap ∧ d+L≤heap ∧ RatAt mem a h L P q ∧ RatAt mem d h L P δ ∧
      RatFits h L P value)
    (fun _ _ _ => True) (fun args _ => 74*args.getD 2 0+60)
    (fun args _ => (if backward then 2*args.getD 2 0 else args.getD 2 0))
  {C with post := fun args mem out final => C.post args mem out final ∧
      out=heapArg args+(if backward then 2*args.getD 2 0 else args.getD 2 0) ∧
      RatAt final (out-args.getD 2 0) h (args.getD 2 0) P value}

/-- Only a deterministic choice of arithmetic is used. -/
theorem roundFlowArithmetic_noRand (add subtract : ℕ) :
    (roundFlowArithmeticBody add subtract).NoRand := by
  simp [roundFlowArithmeticBody,Stmt.NoRand]

private theorem round_add_output {w h L P a b heap v : ℕ} {mem final : ℕ → ℕ} {x y : ℚ}
    (ha : RatAt mem a h L P x) (hb : RatAt mem b h L P y) (hfit : RatFits h L P (x+y))
    (hout : (Num.addContract w h).post [a,b,L,heap] mem v final) :
    v=heap+L ∧ (∀ z<heap,final z=mem z) ∧ ZeroFrom final v ∧ RatAt final heap h L P (x+y) := by
  obtain ⟨hv,_,_,hframe,hzero,hl⟩ := hout
  have he : x+y=((Num.intVal mem a h L+Num.intVal mem b h L:ℤ):ℚ)/(2:ℚ)^P := by
    rw [← ha.2,← hb.2]
    simp only [readRat,Int.cast_add,add_div]
  have hf : Num.Fits h L (Num.intVal mem a h L+Num.intVal mem b h L) :=
    ratFits_numerator (he ▸ hfit)
  have hh : ListAt final heap (Num.digits h L (Num.unsignedVal mem a h L+Num.unsignedVal mem b h L+0)) := hl
  obtain ⟨hvalid,heq⟩ := Num.addCarry_value hh
  simp only [Int.natCast_zero,add_zero,Num.wrap_of_fits hf] at heq
  exact ⟨hv,hframe,hzero,hvalid,by rw [readRat,heq,he]⟩

/-- The direction branch uses exact arithmetic, with at most two
blocks of space and at most 74*L+60 machine steps. -/
theorem roundFlowArithmetic_meetsContract {w h P entry add subtract : ℕ} {p : Program}
    (hBody : p.procs[entry]?=some (roundFlowArithmeticBody add subtract))
    (hAdd : MeetsContract w p add (Num.addContract w h))
    (hSub : MeetsContract w p subtract (Num.subtractContract w h))
    (q δ : ℚ) (backward : Bool) :
    MeetsContract w p entry (roundFlowArithmeticContract w h P q δ backward) := by
  apply meetsContract_of_runs hBody
  intro args mem pos ω hw hpre
  obtain ⟨⟨a,b,L,heap,rfl,ha,hb,hq,hδ,hFit⟩,hz,hSpace⟩ := hpre
  have hWords : ∀ z∈[a,b,L,heap],z<2^w := by
    intro z hz'
    apply hw
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz' ⊢
    tauto
  apply runs_start_le
  unfold roundFlowArithmeticBody
  cases backward with
  | false =>
    change heap+L<2^w at hSpace
    refine runs_cond_le (v:=0) rfl (fun hn => (hn rfl).elim) ?_
    intro _
    refine runs_seq_call_le hAdd (vs:=[a,b,L,heap]) rfl hWords
      ⟨a,b,L,heap,rfl,⟨a,b,L,0,heap,rfl,ha,hb,by decide,hq.1,hδ.1⟩,hz,hSpace⟩ ?_
    intro v final pos' hout
    obtain ⟨he,hframe,hzero,hres⟩ := round_add_output hq hδ hFit hout
    refine runs_ret_le (v:=v) rfl ?_ ?_
    · change (heap≤v ∧ v≤heap+L ∧ (∀ z<heap,final z=mem z) ∧ ZeroFrom final v ∧ True) ∧
        v=heap+L ∧ RatAt final (v-L) h L P (q+δ)
      refine ⟨⟨by omega,he.le,hframe,hzero,trivial⟩,he,?_⟩
      rwa [show v-L=heap by omega]
    · change 0+1+1+4+(38*L+15)+2+2≤74*L+60
      omega
  | true =>
    change heap+2*L<2^w at hSpace
    refine runs_cond_le (v:=1) rfl ?_ (fun he => by contradiction)
    intro _
    refine runs_seq_call_le hSub (vs:=[a,b,L,heap]) rfl hWords
      ⟨⟨a,b,L,heap,rfl,ha,hb,hq.1,hδ.1⟩,hz,hSpace⟩ ?_
    intro v final pos' hout
    obtain ⟨he,hframe,hzero,hres⟩ := round_subtract_output hq hδ hFit hout
    refine runs_ret_le (v:=v) rfl ?_ ?_
    · change (heap≤v ∧ v≤heap+2*L ∧ (∀ z<heap,final z=mem z) ∧ ZeroFrom final v ∧ True) ∧
        v=heap+2*L ∧ RatAt final (v-L) h L P (q-δ)
      refine ⟨⟨by omega,he.le,hframe,hzero,trivial⟩,he,?_⟩
      rwa [show v-L=heap+L by omega]
    · change 0+1+1+4+(74*L+42)+2+2≤74*L+60
      omega

end MinCostFlow.IPM.Machine
