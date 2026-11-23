module

public import MinCostFlow.LastLevelProgram.ScaleWord
public import MinCostFlow.Machine.WideWord.LSSTProgramBase
import WordRAM.Tactic
import Mathlib.Tactic

/-!
# Runtime width for the LSST simulation

The guest of Theorem 2.2 (page 7) uses one-bit limbs. Its simulation
width follows from two binary logarithms of the runtime edge count
and the chosen guest limb count.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM WideWord Scaling.Machine

/-- The guest simulation width is the cited machine's word-size bound
when the cited word-size constant is positive. -/
theorem lsstLSimMin_one_eq (c n m L : ℕ) (hc : 1 ≤ c) :
    lsstLSimMin c n m L 1 =
      c*(Nat.log 2 (6+16*m)+(L+(Nat.log 2 (4*m+2)+1)+2)+3) := by
  unfold lsstLSimMin w'Max kWidthOf
  rw [Nat.mul_one, max_eq_right]
  refine le_trans ?_ (Nat.le_mul_of_pos_left _ hc)
  omega

/-- Arguments are the edge count, guest limb count and the cited
word-size constant. The two logarithm calls use successor arguments. -/
def guestSimulationWidthBody (log : ℕ) : Stmt :=
  .seq (.call 3 log [.bin .add (.bin .mul (.const 4) (.reg 0)) (.const 3)])
  (.seq (.call 4 log [.bin .add (.bin .mul (.const 16) (.reg 0)) (.const 7)])
    (.ret (.bin .mul (.reg 2)
      (.bin .add (.bin .add (.bin .add (.reg 1) (.reg 3)) (.reg 4)) (.const 4)))))

/-- The simulation width is computed with two logarithmic calls and
no memory writes, using a fixed body for every guest limb count. -/
theorem guestSimulationWidth_runs {w log : ℕ} {p : Program}
    (hp : p.HasAt log (clogTwoModule log)) (n m L c pos : ℕ) (mem : ℕ → ℕ)
    (ω : ℕ → Bool) (hc : 1 ≤ c) (_hw : 16 < 2^w) (hm : 16*m+8 < 2^w)
    (hs : lsstLSimMin c n m L 1 < 2^w) :
    ∃ o out cost, Runs w p ω (guestSimulationWidthBody log)
      (startState [m,L,c] mem pos) o out cost ∧
      (o.value = lsstLSimMin c n m L 1 ∧ out.mem = mem) ∧
      cost ≤ 40*(Nat.log 2 (4*m+2)+Nat.log 2 (16*m+6)+2)+65 := by
  let a := Nat.log 2 (4*m+2)+1
  let b := Nat.log 2 (16*m+6)+1
  have ha : Nat.clog 2 (4*m+3) = a := by
    exact clogTwo_succ_eq_log_add_one (n := 4*m+2) (by omega)
  have hb : Nat.clog 2 (16*m+7) = b := by
    exact clogTwo_succ_eq_log_add_one (n := 16*m+6) (by omega)
  have he : lsstLSimMin c n m L 1 = c*(L+a+b+4) := by
    rw [lsstLSimMin_one_eq c n m L hc, show 6+16*m = 16*m+6 by omega]
    dsimp [a,b]
    congr 1
    omega
  have hsum : L+a+b+4 < 2^w := by
    rw [he] at hs
    exact (Nat.le_mul_of_pos_left _ hc).trans_lt hs
  have hcf : c < 2^w := by
    rw [he] at hs
    exact (Nat.le_mul_of_pos_right _ (by omega)).trans_lt hs
  apply runs_start_le
  unfold guestSimulationWidthBody
  refine runs_seq_call_le (clogTwo_meetsContract hp (4*m+3)) (vs := [4*m+3])
    (by eval_expr) (by wram_words) ⟨rfl,by omega,by omega⟩ ?_
  intro r mem₁ pos₁ ⟨hmem₁,hr⟩
  have hr' := hr.trans ha
  subst r
  refine runs_seq_call_le (clogTwo_meetsContract hp (16*m+7)) (vs := [16*m+7])
    (by eval_expr) (by wram_words) ⟨rfl,by omega,by omega⟩ ?_
  intro s mem₂ pos₂ ⟨hmem₂,hs'⟩
  have hs'' := hs'.trans hb
  have hsFit : L+a+s+4 < 2^w := hs''.symm ▸ hsum
  have hvFit : c*(L+a+s+4) < 2^w := by rw [hs'',← he]; exact hs
  refine runs_ret_le (v := c*(L+a+s+4)) (by eval_expr)
    ⟨by rw [Outcome.value,hs'',he],hmem₂.trans hmem₁⟩ ?_
  simp only [clogTwoContract,argsSize,Expr.size,ha,hb,Nat.zero_add,a,b,Nat.mul_add]
  omega

/-- The controller passes the guest limb count and cited constant
along with the number of representative edges. -/
def guestSimulationWidthContract (w n : ℕ) : Contract where
  pre args _ := ∃ m L c, args = [m,L,c] ∧ 1 ≤ c ∧
    16 < 2^w ∧ 16*m+8 < 2^w ∧ lsstLSimMin c n m L 1 < 2^w
  post args mem ret out := ∃ m L c, args = [m,L,c] ∧
    ret = lsstLSimMin c n m L 1 ∧ out = mem
  cost args _ :=
    let m := args.getD 0 0
    40*(Nat.log 2 (4*m+2)+Nat.log 2 (16*m+6)+2)+65

/-- Install the runtime simulation-width procedure in the controller. -/
theorem guestSimulationWidth_meetsContract {w entry log n : ℕ} {p : Program}
    (he : p.procs[entry]? = some (guestSimulationWidthBody log))
    (hp : p.HasAt log (clogTwoModule log)) :
    MeetsContract w p entry (guestSimulationWidthContract w n) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨m,L,c,rfl,hc,hw,hm,hs⟩ := hpre
  obtain ⟨o,out,cost,hr,⟨hout,hmem⟩,hcost⟩ :=
    guestSimulationWidth_runs hp n m L c pos mem ω hc hw hm hs
  exact ⟨o,out,cost,hr,⟨m,L,c,rfl,hout,hmem⟩,hcost⟩

end MinCostFlow.LastLevelProgram
