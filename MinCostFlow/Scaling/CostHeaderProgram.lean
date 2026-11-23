module

public import WordRAM.Layout
import WordRAM.Tactic
import WordRAM.Entry

/-!
# Writing the cost-state header

The cost loop stores a flow pointer, a signed-potential pointer, and the
denominator power in three consecutive fresh words. This procedure writes
that header and returns the new heap, preserving the old memory prefix.
-/

@[expose] public section
namespace MinCostFlow.Scaling.Machine
open WordRAM

/-- Arguments `[flow,potentials,power,heap]`. -/
def costHeaderBody : Stmt :=
  .store (.reg 3) (.reg 0) ;;
  .store (.bin .add (.reg 3) (.const 1)) (.reg 1) ;;
  .store (.bin .add (.reg 3) (.const 2)) (.reg 2) ;;
  .ret (.bin .add (.reg 3) (.const 3))

/-- The header writer occupies one procedure slot. -/
def costHeaderModule : List Stmt := [costHeaderBody]

/-- Three fitting argument words become an exact fresh cost-state header. -/
def costHeaderContract (w : ℕ) : Contract :=
  let H := heapContract w (fun args _ => args.length=4)
    (fun args _ mem' => ListAt mem' (heapArg args) [args.getD 0 0,args.getD 1 0,args.getD 2 0])
    (fun _ _ => 30) (fun _ _ => 3)
  { H with post := fun args mem ret mem' => H.post args mem ret mem' ∧ ret=heapArg args+3 }

/-- Header writing uses no random instruction. -/
theorem costHeaderBody_noRand : costHeaderBody.NoRand := by trivial

/-- The writer stores exactly the three header words in at most 30 steps,
with exact allocation and the shared fresh-heap frame. -/
theorem costHeader_meetsContract {w b : ℕ} {p : Program} (hp : p.HasAt b costHeaderModule) :
    MeetsContract w p b (costHeaderContract w) := by
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨hlen,hz,hs⟩ := hpre
  obtain ⟨flow,pot,power,heap,rfl⟩ : ∃ flow pot power heap,args=[flow,pot,power,heap] := by
    cases args with
    | nil => simp at hlen
    | cons flow rest =>
      cases rest with
      | nil => simp at hlen
      | cons pot rest =>
        cases rest with
        | nil => simp at hlen
        | cons power rest =>
          cases rest with
          | nil => simp at hlen
          | cons heap rest =>
            have hr : rest=[] := by
              cases rest with
              | nil => rfl
              | cons x rest => simp only [List.length_cons] at hlen; omega
            subst rest
            exact ⟨flow,pot,power,heap,rfl⟩
  change ZeroFrom mem heap at hz
  change heap+3<2^w at hs
  have hh : heap<2^w := by omega
  have hh1 : heap+1<2^w := by omega
  have hh2 : heap+2<2^w := by omega
  have hf : flow<2^w := hwords _ (by simp)
  have hpw : pot<2^w := hwords _ (by simp)
  have hpow : power<2^w := hwords _ (by simp)
  have h1 : 1<2^w := by omega
  have h2 : 2<2^w := by omega
  have h3 : 3<2^w := by omega
  apply runs_start_le
  unfold costHeaderBody
  wram_step
  wram_step
  wram_step
  refine runs_ret_le (v := heap+3) (by eval_expr) ?_ ?_
  · change (heap≤heap+3 ∧ heap+3≤heap+3 ∧
      (∀ x<heap,Function.update (Function.update (Function.update mem heap flow) (heap+1) pot) (heap+2) power x=mem x) ∧
      ZeroFrom (Function.update (Function.update (Function.update mem heap flow) (heap+1) pot) (heap+2) power) (heap+3) ∧
      ListAt (Function.update (Function.update (Function.update mem heap flow) (heap+1) pot) (heap+2) power)
        heap [flow,pot,power]) ∧ heap+3=heap+3
    refine ⟨⟨by omega,le_rfl,?_,?_,?_⟩,rfl⟩
    · intro x hx
      simp only [Function.update_of_ne (by omega : x≠heap+2),Function.update_of_ne (by omega : x≠heap+1),
        Function.update_of_ne (by omega : x≠heap)]
    · intro x hx
      simp only [Function.update_of_ne (by omega : x≠heap+2),Function.update_of_ne (by omega : x≠heap+1),
        Function.update_of_ne (by omega : x≠heap)]
      exact hz x (by omega)
    · intro i hi
      have hi' : i=0 ∨ i=1 ∨ i=2 := by change i<3 at hi; omega
      rcases hi' with rfl | rfl | rfl <;>
        simp only [Nat.add_zero,List.getElem_cons_zero,List.getElem_cons_succ,Function.update_self,
          Function.update_of_ne (by omega : heap≠heap+1),Function.update_of_ne (by omega : heap≠heap+2),
          Function.update_of_ne (by omega : heap+1≠heap+2)]
  · simp only [costHeaderContract,heapContract,Expr.size_bin,Expr.size_reg,Expr.size_const]
    decide

/-- Every flow pointer, potential pointer, and denominator power have
simultaneous full header-writer premises on a fresh zero heap. -/
theorem exists_costHeader_pre (flow pot power : ℕ) :
    ∃ w,(∀ a∈[flow,pot,power,0],a<2^w) ∧
      (costHeaderContract w).pre [flow,pot,power,0] (fun _ => 0) := by
  let w := flow+pot+power+4
  have hw : flow+pot+power+4<2^w := Nat.lt_two_pow_self
  refine ⟨w,?_,by rfl,(fun _ _ => rfl),by change 0+3<2^w; omega⟩
  intro a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;> omega

end MinCostFlow.Scaling.Machine
