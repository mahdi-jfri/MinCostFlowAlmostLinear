module

public import MinCostFlow.IPM.Machine.RoundRatFacts
public import MinCostFlow.Num.IsZero
import WordRAM.Tactic
import Mathlib.Tactic.Positivity

/-!
# Reading the dynamic forest's path minimum

The flagged path record identifies the selected edge and its stored
flow and availability. A signed zero test detects an edge that has
become integral and must be cut.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM Rounding

/-- Load the tag and, for an actual hit, test its availability block. -/
def roundPathZeroBody (isZero : ℕ) : Stmt :=
  .cond (.load (.reg 0))
    (.call 2 isZero [.bin .add (.reg 0) (.const 4),.reg 1] ;; .ret (.reg 2))
    (.ret (.const 0))

/-- The zero-availability decision on the decoded path hit. -/
def pathHitZeroValue : Option PathHit → ℕ
  | none => 0
  | some e => if e.avail=0 then 1 else 0

/-- One is returned exactly for a hit with zero availability. -/
def roundPathZeroContract (w h P : ℕ) : Contract where
  pre args mem := ∃ a L hit,args=[a,L] ∧ PathHitAt mem a h L P hit ∧ a+4+2*L<2^w
  post args mem v final :=
    final=mem ∧ ∀ hit, PathHitAt mem (args.getD 0 0) h (args.getD 1 0) P hit →
      v=pathHitZeroValue hit
  cost args _ := 19*args.getD 1 0+30

/-- The tag and zero-test branches are deterministic. -/
theorem roundPathZero_noRand (isZero : ℕ) : (roundPathZeroBody isZero).NoRand := by
  simp [roundPathZeroBody,Stmt.NoRand]

/-- Zero at the rational scale is equivalent to a zero numerator. -/
theorem RatAt.numerator_zero_iff {mem : ℕ → ℕ} {a h L P : ℕ} {q : ℚ}
    (hf : RatAt mem a h L P q) : Num.intVal mem a h L=0 ↔ q=0 := by
  have hd : (2:ℚ)^P≠0 := by positivity
  rw [← hf.2,readRat,div_eq_zero_iff]
  simp [hd]

/-- Reading the first four path record cells gives the tag and the
selected edge's ordered endpoints. -/
theorem pathHit_words {mem : ℕ → ℕ} {a h L P : ℕ} {e : PathHit}
    (hh : PathHitAt mem a h L P (some e)) :
    mem a=1 ∧ mem (a+1)=e.eid ∧ mem (a+2)=e.x ∧ mem (a+3)=e.y := by
  have hl := hh.1
  exact ⟨hl 0 (by simp),hl 1 (by simp),hl 2 (by simp),hl 3 (by simp)⟩

private theorem pathHit_answer_eq {mem : ℕ → ℕ} {a h L P : ℕ} {s t : Option PathHit}
    (hs : PathHitAt mem a h L P s) (ht : PathHitAt mem a h L P t) :
    pathHitZeroValue s=pathHitZeroValue t := by
  cases s with
  | none =>
    cases t with
    | none => rfl
    | some e =>
      have h := (pathHit_words ht).1
      have hz : mem a=0 := hs
      omega
  | some e =>
    cases t with
    | none =>
      have h := (pathHit_words hs).1
      have hz : mem a=0 := ht
      omega
    | some f =>
      simp only [pathHitZeroValue]
      rw [show e.avail=f.avail from hs.2.1.2.symm.trans ht.2.1.2]

/-- Check the exact zero predicate used by Kang and Payor's recursive
path cleanup, at linear cost in the block length. -/
theorem roundPathZero_meetsContract {w h P entry isZero : ℕ} {p : Program}
    (hbody : p.procs[entry]?=some (roundPathZeroBody isZero))
    (hzero : MeetsContract w p isZero (Num.isZeroContract w h)) (hOne : 1<2^w) :
    MeetsContract w p entry (roundPathZeroContract w h P) := by
  apply meetsContract_of_runs hbody
  intro args mem pos ω hwords hpre
  obtain ⟨a,L,hit,rfl,hh,hspace⟩ := hpre
  have ha : a<2^w := hwords _ (by simp)
  have hL : L<2^w := hwords _ (by simp)
  have h4 : 4<2^w := by omega
  have ha4 : a+4<2^w := by omega
  have hLoad : (Expr.load (.reg 0)).eval w (startState [a,L] mem pos)=some (mem a) := by
    eval_expr
  apply runs_start_le
  unfold roundPathZeroBody
  cases hit with
  | none =>
    have hz : mem a=0 := hh
    rw [hz] at hLoad
    refine runs_cond_le (v:=0) hLoad (fun hn => (hn rfl).elim) ?_
    intro _
    refine runs_ret_le (v:=0) (by eval_expr) ⟨rfl,?_⟩ ?_
    · exact fun s hs => pathHit_answer_eq hh hs
    · simp [roundPathZeroContract]
  | some hit =>
    rw [(pathHit_words hh).1] at hLoad
    refine runs_cond_le (v:=1) hLoad ?_ (fun he => by omega)
    intro _
    refine runs_seq_call_le hzero (vs:=[a+4,L]) (by eval_expr) (by wram_words)
      ⟨a+4,L,rfl,by omega,hh.2.1.1⟩ ?_
    intro v final pos' hout
    obtain ⟨hMF,hv⟩ := hout
    have hMem : final=mem := hMF
    subst final
    have hBit : v=(if hit.avail=0 then 1 else 0) := by
      change v=(if Num.intVal mem (a+4) h L=0 then 1 else 0) at hv
      simpa only [hh.2.1.numerator_zero_iff] using hv
    refine runs_ret_le (v:=v) (by eval_expr) ⟨rfl,?_⟩ ?_
    · exact fun s hs => hBit.trans (pathHit_answer_eq hh hs)
    · simp only [roundPathZeroContract,Num.isZeroContract,List.getD_cons_zero,List.getD_cons_succ,
        argsSize_cons,argsSize_nil,Expr.size_bin,Expr.size_const,Expr.size_reg,Expr.size_load]
      omega

end MinCostFlow.IPM.Machine
