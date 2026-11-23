module

public import MinCostFlow.LastLevelProgram.FixedPoint
public import MinCostFlow.Scaling.ClogTwoProgram
import WordRAM.Tactic
import Mathlib.Tactic
import Mathlib.Data.Nat.Size

/-!
# Computing the integer update scale

The denominator of the update in Definition 5.8 (pages 19–20)
uses the binary logarithm of the representative vertex count.
Reuse the verified ceiling-log program at the successor argument.
-/

@[expose] public section

namespace MinCostFlow.LastLevelProgram

open WordRAM Scaling.Machine

/-- The ceiling binary logarithm of a successor is the bit count
of its positive predecessor. -/
theorem clogTwo_succ_eq_log_add_one {n : ℕ} (hn : 0 < n) :
    Nat.clog 2 (n + 1) = Nat.log 2 n + 1 := by
  apply le_antisymm
  · apply Nat.clog_le_of_le_pow
    exact Nat.lt_pow_succ_log_self (by decide : 1 < 2) n
  · apply Nat.succ_le_of_lt
    apply (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr
    exact (Nat.pow_log_le_self 2 hn.ne').trans_lt (Nat.lt_succ_self _)

/-- Compute the scale from arguments `[vertices, edges, constant]`. -/
def scaleWordBody (log : ℕ) : Stmt :=
  .call 3 log [.bin .add (.reg 0) (.const 3)] ;;
  .ret (.bin .mul (.bin .mul (.bin .mul (.const 4) (.reg 2)) (.reg 1))
    (.bin .mul (.reg 3) (.reg 3)))

/-- Compute the exact integer scale in logarithmic time. The checked
output bound also bounds each product in the expression. -/
theorem scaleWord_runs {w log : ℕ} {p : Program}
    (hp : p.HasAt log (clogTwoModule log)) (G : MGraph) (D pos : ℕ)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hD : 1 ≤ D) (hm : 1 ≤ G.m) (hn : G.n + 4 < 2^w)
    (hword : integerScale D G < 2^w) :
    ∃ o st c, Runs w p ω (scaleWordBody log)
      (startState [G.n,G.m,D] mem pos) o st c ∧
      (o.value = integerScale D G ∧ st.mem = mem) ∧
      c ≤ 40 * (Nat.log 2 (G.n + 2) + 1) + 50 := by
  let k := Nat.log 2 (G.n + 2) + 1
  have hk : Nat.clog 2 (G.n + 3) = k :=
    clogTwo_succ_eq_log_add_one (n := G.n + 2) (by omega)
  have hkpos : 1 ≤ k := by dsimp [k]; omega
  have hk2 : 1 ≤ k*k := Nat.mul_pos hkpos hkpos
  have hD4 : 1 ≤ 4*D := Nat.mul_pos (by decide) hD
  have hDm : 1 ≤ 4*D*G.m := Nat.mul_pos hD4 hm
  have hout : 4*D*G.m*(k*k) < 2^w := by
    simpa only [integerScale, k, pow_two] using hword
  have hDmWord : 4*D*G.m < 2^w := (Nat.le_mul_of_pos_right _ hk2).trans_lt hout
  have hDWord : 4*D < 2^w := (Nat.le_mul_of_pos_right _ hm).trans_lt hDmWord
  have hkWord : k*k < 2^w := (Nat.le_mul_of_pos_left _ hDm).trans_lt hout
  have hkWord' : k < 2^w := (Nat.le_mul_of_pos_right _ hkpos).trans_lt hkWord
  have hmWord : G.m < 2^w := (Nat.le_mul_of_pos_left _ hD4).trans_lt hDmWord
  have hDWord' : D < 2^w := (Nat.le_mul_of_pos_left _ (by decide : 0 < 4)).trans_lt hDWord
  have h4 : 4 < 2^w := (Nat.le_mul_of_pos_right _ hD).trans_lt hDWord
  apply runs_start_le
  unfold scaleWordBody
  refine runs_seq_call_le (clogTwo_meetsContract hp (G.n + 3)) (vs := [G.n+3])
    (by eval_expr) ?_ ?_ ?_
  · wram_words
  · exact ⟨rfl,by omega,by omega⟩
  · intro ret out pos' ⟨hmem, hret⟩
    have hr : ret = k := hret.trans hk
    have hretWord : ret < 2^w := hr ▸ hkWord'
    have hprod : ret * ret < 2^w := by rw [hr]; exact hkWord
    have hresult : 4*D*G.m*(ret*ret) < 2^w := by rw [hr]; exact hout
    refine runs_ret_le (v := 4*D*G.m*(ret*ret)) (by eval_expr) ?_ ?_
    · refine ⟨?_,hmem⟩
      change 4*D*G.m*(ret*ret) = integerScale D G
      rw [hr]
      simp only [integerScale, k, pow_two]
    · simp [clogTwoContract, argsSize, Expr.size, hk, k]
      omega

/-- The fixed-point grid can fall between four-bit limb boundaries
even on a connected graph consisting of one edge. -/
theorem weightPrecision_singleEdge_not_limbAligned (G : MGraph)
    (hn : G.n = 2) (hm : G.m = 1) :
    weightPrecision 1 G = 7 ∧ ¬ (4 : ℕ) ∣ weightPrecision 1 G := by
  have hceil : ⌈max 1 (1 : ℝ)⌉₊ = 1 := by norm_num
  have hprec : weightPrecision 1 G = 7 := by
    rw [weightPrecision, hceil, integerScale, hn, hm]
    decide
  exact ⟨hprec, hprec.symm ▸ (by decide : ¬ (4 : ℕ) ∣ 7)⟩

/-- Compute the grid precision from the scale word. -/
def precisionWordBody (log : ℕ) : Stmt :=
  .call 1 log [.bin .add (.bin .mul (.const 2) (.reg 0)) (.const 1)] ;;
  .ret (.reg 1)

/-- The machine's precision is the bit length of twice the scale. -/
theorem precisionWord_runs {w log : ℕ} {p : Program}
    (hp : p.HasAt log (clogTwoModule log)) (scale pos : ℕ)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hpos : 0 < scale) (hroom : 2 * scale + 2 < 2^w) :
    ∃ o st cost, Runs w p ω (precisionWordBody log)
      (startState [scale] mem pos) o st cost ∧
      (o.value = (2 * scale).size ∧ st.mem = mem) ∧
      cost ≤ 40 * (2 * scale).size + 35 := by
  let n := 2 * scale
  have hn : 0 < n := by dsimp [n]; omega
  have hlog : Nat.clog 2 (n + 1) = n.size := by
    rw [clogTwo_succ_eq_log_add_one hn]
    apply le_antisymm
    · exact Nat.succ_le_of_lt (Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne'))
    · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)
  have hlogword : Nat.clog 2 (n + 1) < 2^w := by
    have hle : Nat.clog 2 (n + 1) ≤ n + 1 := Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
    dsimp [n] at hle ⊢
    omega
  apply runs_start_le
  unfold precisionWordBody
  refine runs_seq_call_le (clogTwo_meetsContract hp (n + 1)) (vs := [n+1])
    (by dsimp [n]; eval_expr) ?_ ?_ ?_
  · dsimp [n]; wram_words
  · exact ⟨rfl, hroom, by omega⟩
  · intro ret out pos' ⟨hmem,hret⟩
    have hretWord : ret < 2^w := hret ▸ hlogword
    refine runs_ret_le (v := ret) (by eval_expr) ⟨hret.trans hlog,hmem⟩ ?_
    simp [clogTwoContract, argsSize, Expr.size, hlog, n]
    omega

/-- The precision computed from the canonical scale is the precision
used by the fixed-point last-level model. -/
theorem precisionWord_eq_model (C : ℝ) (G : MGraph) :
    (2 * integerScale ⌈max 1 C⌉₊ G).size = weightPrecision C G := by
  rfl

/-- Compute the bit count of the round-independent weight numerator
bound without materializing its potentially multiword value. -/
def weightBoundWidthBody (log : ℕ) : Stmt :=
  .seq (.call 2 log [.bin .add (.bin .mul (.const 2) (.reg 0)) (.const 1)])
    (.ret (.bin .add (.reg 2) (.reg 1)))

/-- At a live round the edge count is positive. The initial width for
the guest scan is the bit count of `2*m*2^Q`. -/
theorem weightBoundWidth_runs {w log : ℕ} {p : Program}
    (hp : p.HasAt log (clogTwoModule log)) (m Q pos : ℕ)
    (mem : ℕ → ℕ) (ω : ℕ → Bool)
    (hm : 0 < m) (hroom : 2*m+2 < 2^w)
    (hQ : (2*m).size+Q < 2^w) :
    ∃ o st cost, Runs w p ω (weightBoundWidthBody log)
      (startState [m,Q] mem pos) o st cost ∧
      (o.value = (2*m*2^Q).size ∧ st.mem = mem) ∧
      cost ≤ 40*(2*m).size+37 := by
  let n := 2*m
  have hn : 0 < n := by dsimp [n]; omega
  have hlog : Nat.clog 2 (n+1) = n.size := by
    rw [clogTwo_succ_eq_log_add_one hn]
    apply le_antisymm
    · exact Nat.succ_le_of_lt (Nat.lt_size.mpr (Nat.pow_log_le_self 2 hn.ne'))
    · exact Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide : 1 < 2) n)
  have hsize : (2*m*2^Q).size = n.size+Q := by
    change (n*2^Q).size = _
    rw [← Nat.shiftLeft_eq,Nat.size_shiftLeft hn.ne']
  apply runs_start_le
  unfold weightBoundWidthBody
  refine runs_seq_call_le (clogTwo_meetsContract hp (n+1)) (vs := [n+1])
    (by dsimp [n]; eval_expr) ?_ ⟨rfl,hroom,by omega⟩ ?_
  · dsimp [n]; wram_words
  · intro ret out pos' ⟨hmem,hret⟩
    have hret' : ret = n.size := hret.trans hlog
    have hretFit : ret+Q < 2^w := hret'.symm ▸ hQ
    refine runs_ret_le (v := ret+Q) (by eval_expr) ⟨?_,hmem⟩ ?_
    · exact (congrArg (·+Q) hret').trans hsize.symm
    · simp [clogTwoContract,argsSize,Expr.size,hlog,n]
      omega

/-- Callable interface for the weight bound's bit count. -/
def weightBoundWidthContract (w : ℕ) : Contract where
  pre args _ := ∃ m Q, args = [m,Q] ∧ 0 < m ∧ 2*m+2 < 2^w ∧ (2*m).size+Q < 2^w
  post args mem ret out := ∃ m Q, args = [m,Q] ∧ ret = (2*m*2^Q).size ∧ out = mem
  cost args _ := 40*(2*args.getD 0 0).size+37

/-- Install the initial-width calculation using the linked ceiling logarithm. -/
theorem weightBoundWidth_meetsContract {w entry log : ℕ} {p : Program}
    (he : p.procs[entry]? = some (weightBoundWidthBody log))
    (hp : p.HasAt log (clogTwoModule log)) :
    MeetsContract w p entry (weightBoundWidthContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨m,Q,rfl,hm,hroom,hQ⟩ := hpre
  obtain ⟨o,out,c,hrun,hpost,hcost⟩ := weightBoundWidth_runs hp m Q pos mem ω hm hroom hQ
  exact ⟨o,out,c,hrun,⟨m,Q,rfl,hpost⟩,hcost⟩

/-- Compute the integer update scale from the representative counts. -/
def scaleWordContract (w : ℕ) (G : MGraph) : Contract where
  pre args _ := ∃ D, args = [G.n,G.m,D] ∧ 1 ≤ D ∧ 1 ≤ G.m ∧
    G.n+4 < 2^w ∧ integerScale D G < 2^w
  post args mem ret out := ∃ D, args = [G.n,G.m,D] ∧
    ret = integerScale D G ∧ out = mem
  cost _ _ := 40*(Nat.log 2 (G.n+2)+1)+50

/-- Install the update scale calculation as a runtime call. -/
theorem scaleWord_meetsContract {w entry log : ℕ} {p : Program} (G : MGraph)
    (he : p.procs[entry]? = some (scaleWordBody log))
    (hp : p.HasAt log (clogTwoModule log)) :
    MeetsContract w p entry (scaleWordContract w G) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨D,rfl,hD,hm,hn,hfit⟩ := hpre
  obtain ⟨o,out,cost,hr,hpost,hcost⟩ := scaleWord_runs hp G D pos mem ω hD hm hn hfit
  exact ⟨o,out,cost,hr,⟨D,rfl,hpost⟩,hcost⟩

/-- Compute the grid precision from the scale word. -/
def precisionWordContract (w : ℕ) : Contract where
  pre args _ := ∃ scale, args = [scale] ∧ 0 < scale ∧ 2*scale+2 < 2^w
  post args mem ret out := ∃ scale, args = [scale] ∧ ret = (2*scale).size ∧ out = mem
  cost args _ := 40*(2*args.getD 0 0).size+35

/-- Install the runtime grid precision calculation. -/
theorem precisionWord_meetsContract {w entry log : ℕ} {p : Program}
    (he : p.procs[entry]? = some (precisionWordBody log))
    (hp : p.HasAt log (clogTwoModule log)) :
    MeetsContract w p entry (precisionWordContract w) := by
  apply meetsContract_of_runs he
  intro args mem pos ω _ hpre
  obtain ⟨scale,rfl,hpos,hfit⟩ := hpre
  obtain ⟨o,out,cost,hr,hpost,hcost⟩ := precisionWord_runs hp scale pos mem ω hpos hfit
  exact ⟨o,out,cost,hr,⟨scale,rfl,hpost⟩,hcost⟩

end MinCostFlow.LastLevelProgram
