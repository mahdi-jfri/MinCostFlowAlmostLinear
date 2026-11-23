module

public import MinCostFlow.IPM.Machine.PrecisionParameters
public import MinCostFlow.Num.IPM.BitLength
import MinCostFlow.Num.ModulePlacement
import WordRAM.Tactic
import Mathlib.Tactic.Ring

/-!
# Computing the slack range exponent on the machine

Two verified binary-length scans determine the range exponent derived
from the potential. The remaining arithmetic uses word operations, whose
intermediate values are bounded by the chosen exponent. No real logarithm
is computed. Memory is unchanged and every random tape has the same run.
-/

@[expose] public section
namespace MinCostFlow.IPM.Machine
open WordRAM

/-- Arguments `[m,U]`. Return `220000(size m+size U)²`. -/
def precisionRangeBody (bits : ℕ) : Stmt :=
  .call 2 bits [.reg 0] ;;
  .call 3 bits [.reg 1] ;;
  .ret (.bin .mul (.const 220000)
    (.bin .mul (.bin .add (.reg 2) (.reg 3)) (.bin .add (.reg 2) (.reg 3))))

/-- Range-exponent entry and the shared binary-length scanner. -/
def precisionRangeModule (b : ℕ) : List Stmt :=
  [precisionRangeBody (b+1)] ++ Num.IPM.bitLengthModule (b+1)

/-- Read-only computation, with explicit scan and arithmetic cost. -/
def precisionRangeContract (w : ℕ) : Contract where
  pre args _ := ∃ m U,args=[m,U] ∧ 2 ≤ m*U ∧ slackRangeExponent m U < 2^w
  post args mem v mem' := mem'=mem ∧ v=slackRangeExponent (args.getD 0 0) (args.getD 1 0)
  cost args _ := 14*((args.getD 0 0).size+(args.getD 1 0).size)+100

/-- Parameter selection contains no random instruction. -/
theorem precisionRangeModule_noRand (b : ℕ) :
    ∀ body ∈ precisionRangeModule b,body.NoRand := by
  intro body hb
  simp only [precisionRangeModule,List.mem_append,List.mem_singleton] at hb
  rcases hb with rfl | hb
  · simp [precisionRangeBody,Stmt.NoRand]
  · exact Num.IPM.bitLengthModule_noRand _ _ hb

/-- The machine computes the chosen range exponent in linear time in
input bit lengths. All intermediate arithmetic fits in one word. -/
theorem precisionRange_meetsContract {w b : ℕ} {p : Program}
    (hw : 2 < 2^w) (hp : p.HasAt b (precisionRangeModule b)) :
    MeetsContract w p b (precisionRangeContract w) := by
  have hbits : p.HasAt (b+1) (Num.IPM.bitLengthModule (b+1)) :=
    Num.hasAt_append_right hp
  have hbitSpec := Num.IPM.bitLength_meetsContract hw hbits
  apply meetsContract_of_runs hp.head
  intro args mem pos ω hwords hpre
  obtain ⟨m,U,rfl,hsize,hE⟩ := hpre
  have hmw : m < 2^w := hwords _ (by simp)
  have hUw : U < 2^w := hwords _ (by simp)
  have hm : 0 < m := Nat.pos_of_ne_zero (by intro hz; simp [hz] at hsize)
  have hb : 1 ≤ m.size+U.size := by have hh := Nat.size_pos.mpr hm; omega
  have hbsq : m.size+U.size ≤ (m.size+U.size)^2 := by nlinarith only [hb]
  have hsqpos : 1 ≤ (m.size+U.size)^2 := by omega
  have hconst : 220000 < 2^w := by unfold slackRangeExponent at hE; omega
  have hsum : m.size+U.size < 2^w := by unfold slackRangeExponent at hE; omega
  have hsquare : (m.size+U.size)*(m.size+U.size) < 2^w := by
    rw [← pow_two]
    unfold slackRangeExponent at hE
    omega
  apply runs_start_le
  unfold precisionRangeBody
  refine runs_seq_call_le hbitSpec (vs := [m]) (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨m,rfl⟩
  · intro vm mem1 pos1 hp1
    obtain ⟨rfl,hvm⟩ := hp1
    change vm=m.size at hvm
    subst vm
    refine runs_seq_call_le hbitSpec (vs := [U]) (by eval_expr) ?_ ?_ ?_
    · wram_words
    · exact ⟨U,rfl⟩
    · intro vU mem2 pos2 hp2
      obtain ⟨rfl,hvU⟩ := hp2
      change vU=U.size at hvU
      subst vU
      have hprod : 220000*((m.size+U.size)*(m.size+U.size)) < 2^w := by
        simpa only [slackRangeExponent,pow_two] using hE
      refine runs_ret_le (v := slackRangeExponent m U) ?_ ?_ ?_
      · unfold slackRangeExponent
        rw [pow_two]
        eval_expr
      · exact ⟨rfl,rfl⟩
      · simp [precisionRangeContract,Num.IPM.bitLengthContract,argsSize,
          Expr.size_bin,Expr.size_const,Expr.size_reg,startState]
        omega

/-- The chosen parameter word width discharges the range scanner's
arithmetic fit premise. The two input words retain their usual fit check. -/
theorem precisionRange_pre_of_parameter_width (m U : ℕ) {w : ℕ}
    (hw : ipmParameterWordBits m U ≤ w) (hsize : 2 ≤ m*U) (mem : ℕ → ℕ) :
    (precisionRangeContract w).pre [m,U] mem := by
  have hr := (ipm_parameter_words_fit m U hw).2.2.2.1
  have he : slackRangeExponent m U ≤ ipmRangeExponent m U := by
    unfold ipmRangeExponent
    omega
  exact ⟨m,U,rfl,hsize,he.trans_lt hr⟩

/-- The range-selection preconditions hold jointly on a concrete input,
and the actual program terminates for every random tape. -/
theorem precisionRange_example :
    let p : Program := ⟨precisionRangeModule 0⟩
    p.IsDeterministic ∧ ∀ ω : ℕ → Bool,
      ∃ o st c, Runs 24 p ω (precisionRangeBody 1)
        (startState [1,2] (fun _ => 0) 0) o st c ∧
        o.value=1980000 ∧ st.mem=(fun _ => 0) ∧ c ≤ 142 := by
  dsimp only
  have hplace : (⟨precisionRangeModule 0⟩ : Program).HasAt 0 (precisionRangeModule 0) := by
    intro i hi
    simp only [Nat.zero_add,List.getElem?_eq_getElem hi]
  have hmet := precisionRange_meetsContract (by decide : 2 < 2^24) hplace
  constructor
  · exact precisionRangeModule_noRand 0
  · intro ω
    have hpre : (precisionRangeContract 24).pre [1,2] (fun _ => 0) := by
      refine ⟨1,2,rfl,by decide,?_⟩
      decide
    obtain ⟨body,hbody,o,st,c,hr,hpost,hcost⟩ := hmet [1,2] (fun _ => 0) 0 ω
      (by intro x hx; simp at hx; rcases hx with rfl | rfl <;> decide) hpre
    have he : body=precisionRangeBody 1 := by simpa [precisionRangeModule] using hbody.symm
    subst body
    refine ⟨o,st,c,hr,?_,hpost.1,?_⟩
    · simpa [precisionRangeContract,slackRangeExponent,show Nat.size 1=1 by decide,show Nat.size 2=2 by decide] using hpost.2
    · simpa [precisionRangeContract,show Nat.size 1=1 by decide,show Nat.size 2=2 by decide] using hcost

end MinCostFlow.IPM.Machine
